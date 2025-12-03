#!/usr/bin/env python
# coding: utf-8


import customtkinter as ctk
import tkinter as tk
from CTkScrollableDropdown import *
from tkinter import filedialog, messagebox
import pandas as pd
import pymssql as pyms
from datetime import datetime, timedelta, timezone

import json
import datetime as dt
import os
from PIL import Image
import logging
import traceback
import sys
from pathlib import Path
from functools import wraps
import time
import re


# Create a custom exception hook to log any unhandled exceptions
def exception_handler(exctype, value, tb):
    """
    Global exception handler to catch and log all unhandled exceptions
    """
    logger = logging.getLogger("LindeDataValidationTool")
    
    # Format the exception traceback
    exception_details = ''.join(traceback.format_exception(exctype, value, tb))
    
    # Log the exception
    logger.critical(f"Unhandled exception: {value}\n{exception_details}")
    
    # Call the default exception handler
    sys.__excepthook__(exctype, value, tb)

def setup_logging():
    """Set up logging configuration with enhanced error capture"""
    # Create logs directory if it doesn't exist
    logs_dir = Path("logs")
    logs_dir.mkdir(exist_ok=True)
    
    # Create log file with timestamp in name
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_file = logs_dir / f"validation_tool_{timestamp}.log"
    
    # Configure logger - set level to DEBUG to capture everything
    logging.basicConfig(
        level=logging.DEBUG,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
        handlers=[
            logging.FileHandler(log_file, encoding='utf-8')
        ]
    )
    
    # Set up the global exception hook
    sys.excepthook = exception_handler
    
    # Get the application logger
    logger = logging.getLogger("LindeDataValidationTool")
    logger.info(f"Application started. Log file: {log_file}")
    
    return logger

# Decorator to log exceptions in functions
def log_exceptions(func):
    """Decorator to log exceptions raised in functions"""
    @wraps(func)
    def wrapper(*args, **kwargs):
        logger = logging.getLogger("LindeDataValidationTool")
        try:
            return func(*args, **kwargs)
        except Exception as e:
            logger.error(f"Exception in {func.__name__}: {str(e)}")
            logger.error(traceback.format_exc())
            raise  # Re-raise the exception after logging
    return wrapper

# Global logger
logger = setup_logging()


# #========================== Utilities =====================

def convertDateTime(timevalue, fromTimeZone, toTimeZone):
    return fromTimeZone.normalize(fromTimeZone.localize(timevalue)).astimezone(toTimeZone)

def local_to_utc(df: pd.DataFrame, from_offset_hours: int) -> pd.DataFrame:
    """
    Convert a timestamp column from a local UTC offset to UTC.

    Args:
        df: DataFrame with a datetime column named TIMESTAMP.
        from_offset_hours: Local timezone offset in hours (e.g. 2 for UTC+2).

    Returns:
        DataFrame with TIMESTAMP column converted to UTC.
    """
    local_tz = timezone(timedelta(hours=from_offset_hours))
    logging.info(f"Local UTC format chosen: {local_tz}")
    return df[TIMESTAMP].dt.tz_localize(local_tz).dt.tz_convert(timezone.utc) #AE DB default timezone



def loadConfiguration():
    try:
        with open("appsettings.prod.json") as f:
            config = json.load(f)            
    except Exception as e:
        raise RuntimeError(f"Error occured while loadConfiguration(){e}")
    return config

UTC_OFFSETS = {
    "UTC-12": -12, "UTC-11": -11, "UTC-10": -10, "UTC-9": -9,
    "UTC-8": -8, "UTC-7": -7, "UTC-6": -6, "UTC-5": -5, "UTC-4": -4,
    "UTC-3": -3, "UTC-2": -2, "UTC-1": -1, "UTC+0": 0,
    "UTC+1": 1, "UTC+2": 2, "UTC+3": 3, "UTC+4": 4, "UTC+5": 5,
    "UTC+6": 6, "UTC+7": 7, "UTC+8": 8, "UTC+9": 9, "UTC+10": 10,
    "UTC+11": 11, "UTC+12": 12
}

# == Specific column names 

SUPPRESSED = "Suppressed"
SUPPRESSED_TYPE = "SuppressedType"
UNSUPPRESSED_TIME ="UnsuppressedTime"
MESSAGE_TYPE = "MessageType"
CONDITION = "Condition"
SUBCONDITION = "SubCondition"
IS_ALARM = "Alarm"
EVENT_CATEGORY = "EventCategory"


try:
    config = loadConfiguration()
    aeu_config = config["aeu"]
    #UI layout colors
    color_config = config["colors"]
    category_by_AE = [aeu_config["C_TAG"]]
    # Used for Class filtering to make IS_ALARM column     
    alarmClasses = config["alarmClasses"]
    
    # load AEreaderDB HEARTBEATS format
    aereader_hb = config["aereporting_db_columns"]["aereader_hb"] #"AeReader::AEHEARTBEAT"
    dcs_hb_aedb = config["aereporting_db_columns"]["dcs_hb"] #"::AEHEARTBEAT/I"
    
    # load Pcs7 HEARTBEAT format
    dcs_hb = config["pcs7_columns"]["dcs_hb"] # "AEHEARTBEAT/I"
    
    # default AEDatabase format
    outputTimeZone = aeu_config["AEDB_timezone"]
    # default timezone in UI
    defaultTimeZone= aeu_config["default_UI_timezone"]
    dateTimeFormat = aeu_config["DT_FORMAT"]

except Exception as e:
    logging.error(f"Error occured while loadConfiguration(). Check appsettings.prod.json file: {e}")


# AeReader processing functions
sqlQuery="""
    SELECT     
        [Alarm_Id] AS ID
        ,[DisplayName] AS Plant
        ,[Alarm_Type] AS MessageType        
        ,[Start_Time] AS [StartTime]        
        ,[Ack_Time] AS [AckTime]        
        ,[End_Time] AS [EndTime]  
        ,[Alarm_Desc] AS Message
        ,[Severity]
        ,[Historian_Quality] AS Quality
        ,[EventCategory] AS [EventCategory]
        ,[Condition]
        ,[SubCondition]                    
        ,[Source]
        ,[DataSource]   
        ,[CustomSuppressed] AS Suppressed
        ,[CustomSuppressedType] AS SuppressedType
        ,[CustomUnsuppressedTime] AS UnsuppressedTime   
    FROM [dbo].[vwLindeAlarmsSPKD] almData WITH(NOLOCK)    
    WHERE [DisplayName] = '{}' AND Start_Time >= '{}' AND Start_Time <= '{}' AND Historian_Quality = 'Good'
"""
sqlQueryHint = """SELECT DISTINCT [DisplayName] AS Plant
FROM [dbo].[vwLindeAlarmsSPKD] almData WITH(NOLOCK)
WHERE [DisplayName] LIKE '%{}%' AND Start_Time >= '{}' AND Start_Time <= '{}'"""


# Load sqlQueries from AE Database
@log_exceptions
def loadData(plant, fromTime, toTime, server, port, db, isDebug):
    retries = 0
    MAX_RETRIES = 2
    TIMEOUT = 7  # seconds
    while retries < MAX_RETRIES:
        try:
            data = []
            hint_message = ""
            with pyms.connect(server=server, port=port, database=db, timeout=TIMEOUT) as con:
                with con.cursor(as_dict=True) as cursor:
                    if isDebug:
                        print(sqlQuery.format(plant, fromTime, toTime))
                    else:
                        cursor.execute(sqlQuery.format(plant, fromTime.strftime(dateTimeFormat), toTime.strftime(dateTimeFormat)))
                        for row in cursor:
                            data.append(row)
                        if not data:
                            cursor.execute(sqlQueryHint.format(plant, fromTime.strftime(dateTimeFormat), toTime.strftime(dateTimeFormat)))
                            hint_data = []
                            for row in cursor:
                                hint_data.append(row)
                            if hint_data:
                                available_plants = [row['Plant'] for row in hint_data]
                                hint_message = f"No exact match found for '{plant}'. Did you mean one of these? {', '.join(available_plants)}"
            
            df = pd.DataFrame(data)
            logger.info(f"Query returned {len(df)} rows")
            del data
            
            return df, hint_message
        
        except pyms.OperationalError as e:
            retries += 1
            logger.warning(f"Attempt {retries} failed: {e}")
            if retries < MAX_RETRIES:
                time.sleep(2 ** retries)  # Exponential backoff
            else:
                logger.error(f"Max retries reached. Failed to load data for plant: {plant}")
                raise
        except Exception as e:
            logger.error(f"Unexpected error: {e}")
            raise


# Function filtering AE DataFrame for final result
@log_exceptions
def transfer_aereporting_df(df,ftz):
    #ftz = pytz.timezone(ftz)
    df[aeu_config["C_STARTTIME"]] = pd.to_datetime(df[aeu_config["C_STARTTIME"]])
    # df[aeu_config["C_STARTTIME"]] = df[aeu_config["C_STARTTIME"]].dt.tz_localize(None)
    # df[aeu.C_STARTTIME] = df.apply(lambda row: aeu.convertDateTime(row[aeu.C_STARTTIME],ftz,ttz), axis=1)

    df[aeu_config["C_ACKTIME"]] = pd.to_datetime(df[aeu_config["C_ACKTIME"]])
    #df[aeu_config["C_ACKTIME"]] = df[aeu_config["C_ACKTIME"]].dt.tz_localize(None)
    #df[aeu_config["C_ACKTIME"]] = df.apply(lambda row: convertDateTime(row[aeu_config["C_ACKTIME"]],ftz,ttz) if (pd.isna(row[aeu_config["C_ACKTIME"]])==False) and (row[aeu_config["C_ACKTIME"]].tzinfo is not None) else row[aeu_config["C_ACKTIME"]], axis=1)

    df[aeu_config["C_ENDTIME"]] = pd.to_datetime(df[aeu_config["C_ENDTIME"]])
    #df[aeu_config["C_ENDTIME"]] = df[aeu_config["C_ENDTIME"]].dt.tz_localize(None)
    #df[aeu_config["C_ENDTIME"]] = df.apply(lambda row: convertDateTime(row[aeu_config["C_ENDTIME"]],ftz,ttz) if (pd.isna(row[aeu_config["C_ENDTIME"]])==False) and (row[aeu_config["C_ENDTIME"]].tzinfo is not None) else row[aeu_config["C_ENDTIME"]], axis=1)

    df[UNSUPPRESSED_TIME] = pd.to_datetime(df[UNSUPPRESSED_TIME])
    #df[UNSUPPRESSED_TIME] = df[UNSUPPRESSED_TIME].dt.tz_localize(None)
    #df[UNSUPPRESSED_TIME] = df.apply(lambda row: convertDateTime(row[UNSUPPRESSED_TIME],ftz,ttz) if (pd.isna(row[UNSUPPRESSED_TIME])==False) and (row[UNSUPPRESSED_TIME].tzinfo is not None) else row[UNSUPPRESSED_TIME] , axis=1)
        
    # add Station, Area and tag info from source   
    df[aeu_config["C_STATION"]]=None 
    df[aeu_config["C_AREA"]]=None 
    df[aeu_config["C_TAG"]]=None 
    
    for index, row in df.iterrows():    
        tokens = row[aeu_config["C_SOURCE"]].split('::')   # station, area, tag     
        if len(tokens)>=1:        
            df.loc[index,aeu_config["C_STATION"]] = tokens[0]
        
        if len(tokens)>1:
            df.loc[index,aeu_config["C_AREA"]] = tokens[1]

        if len(tokens)>2:
            df.loc[index,aeu_config["C_TAG"]] = tokens[2]
            
    df = df.sort_values(by="StartTime")
    
    # filter or skip "unwanted" acknowledgment from EventCategory
    event_category_filter = ["System, does not require acknowledgment"]
    df = df[~df[EVENT_CATEGORY].isin(event_category_filter)]
    
    # filter rows Where quality is BAD

    #reordering columns                                                                     
    colNames = [aeu_config["C_STARTTIME"], aeu_config["C_TAG"], aeu_config["C_AREA"], 
        aeu_config["C_STATION"], "EventCategory", "Condition", "SubCondition", 
        aeu_config["C_MESSAGE"], "MessageType", aeu_config["C_SEVERITY"],               #----mby change this
        aeu_config["C_ACKTIME"], aeu_config["C_ENDTIME"], "Suppressed",
        "SuppressedType", "UnsuppressedTime", aeu_config["C_SOURCE"], 
        PLANT, "DataSource", "ID"]
 
    df = df.loc[:,colNames]
    return df

# == Show statistics
@log_exceptions
def show_ae_statistics(df):
    report = {}
    eventCategory_alarms = ["P3_P4", "PLC"]
    eventCategory_alarms_lower = [ec.lower() for ec in eventCategory_alarms]
    
    alarmCount = 0
    
    if IS_ALARM in df[MESSAGE_TYPE].values:
        alarmCount = len(df[df[MESSAGE_TYPE] == IS_ALARM]) 
    else:
        pattern = '|'.join(eventCategory_alarms_lower)
        alarm_mask = df[EVENT_CATEGORY].str.lower().str.contains(
            pattern, case=False, regex=True
        ) #na=False
        alarmCount = alarm_mask.sum()
    
    eventCount = df.shape[0] - alarmCount
    # Modified dcs_hb counting logic
    dcs_hb_pattern = '|'.join([re.escape(hb) for hb in dcs_hb_aedb])
    dcshb_mask = df[SOURCE].str.contains(dcs_hb_pattern, case=False, regex=True, na=False)
    dcshbCount = dcshb_mask.sum()
    aehbCount = len(df[df[aeu_config["C_SOURCE"]].str.contains(aereader_hb, case=False)])
    
    report[aeu_config["SI_MODULE_NAME"]] = aeu_config["SI_MODULE_AEREPORT"]
    report[aeu_config["SI_FIRST_REC"]] = df.StartTime.iat[0].tz_localize(None)
    report[aeu_config["SI_LAST_REC"]] = df.StartTime.iat[-1].tz_localize(None)
    report[aeu_config["SI_QTY_MES"]] = df.shape[0]
    report[aeu_config["SI_QTY_AMES"]] = alarmCount
    report[aeu_config["SI_QTY_EMES"]] = eventCount
    report[aeu_config["SI_QTY_DCS_EMES"]] = eventCount - dcshbCount - aehbCount
    report[aeu_config["SI_QTY_DCS_HB"]] = dcshbCount
    report[aeu_config["SI_QTY_AER_HB"]] = aehbCount
    
    # == Alarms statistics by CATEGORY_BY
    # First try filtering by MESSAGE_TYPE, then fall back to EVENT_CATEGORY if needed
    if IS_ALARM in df[MESSAGE_TYPE].values:
        alarm_df = df[df[MESSAGE_TYPE] == IS_ALARM]
    else:
        pattern = '|'.join(eventCategory_alarms_lower)
        alarm_mask = df[EVENT_CATEGORY].str.lower().str.contains(
            pattern, case=False, regex=True
        )
        alarm_df = df[alarm_mask]
    
    gdf = alarm_df.groupby(category_by_AE).count()
    gdf.rename(columns={MESSAGE_TYPE: 'Qty'}, inplace=True)
    gdf = gdf.sort_values(['Qty', gdf.index.name], ascending=False)
    gdf = gdf['Qty']

    pgdf = gdf.reset_index()
    report[aeu_config["SI_TOPX_ALARMS"]] = pgdf.values.tolist()
    
    # == Events statistics by CATEGORY_BY
    # First try filtering by MESSAGE_TYPE, then fall back to EVENT_CATEGORY if needed
    if IS_ALARM in df[MESSAGE_TYPE].values:
        event_df = df[df[MESSAGE_TYPE] != IS_ALARM]
    else:
        pattern = '|'.join(eventCategory_alarms_lower)
        event_mask = ~df[EVENT_CATEGORY].str.lower().str.contains(
            pattern, case=False, regex=True
        )
        event_df = df[event_mask]
    
    gdf = event_df.groupby(category_by_AE).count()
    gdf.rename(columns={MESSAGE_TYPE: 'Qty'}, inplace=True)
    gdf = gdf.sort_values(['Qty', gdf.index.name], ascending=False)
    gdf = gdf['Qty']

    pgdf = gdf.reset_index()
    report[aeu_config["SI_TOPX_EVENTS"]] = pgdf.values.tolist()
    
    # Prepare report df to be stored as csv
    report_df = pd.DataFrame([report])
    report_df = report_df.map(lambda x: x.encode('unicode_escape').decode('utf-8') if isinstance(x, str) else x)
    
    # Create formatted display string
    stats_display = f"""
        First message time: {report[aeu_config["SI_FIRST_REC"]]}
        Last message time: {report[aeu_config["SI_LAST_REC"]]}

        Number of messages: {report[aeu_config["SI_QTY_MES"]]}
        Number of alarms: {report[aeu_config["SI_QTY_AMES"]]}
        Number of events: {report[aeu_config["SI_QTY_EMES"]]}
        - thereof:
            Number of DCS events: {report[aeu_config["SI_QTY_DCS_EMES"]]}
            Number of DCS Heartbeats: {report[aeu_config["SI_QTY_DCS_HB"]]}
            Number of AE Heartbeats: {report[aeu_config["SI_QTY_AER_HB"]]}
        """
    
    return report_df, stats_display, dcshbCount


# #=========================== RawPcs7 Settings =======================


# == Specific column names for PCS7 

STATUS = 'Status' #previously it was STATE="State"
AREA = 'Area'
CLASS = 'Class'
TIMESTAMP = 'Timestamp'
TYPE= 'Type'
NUMBER = "Number" # new
SOURCE = "Source" # Previously it was TAG
EVENT = "Event"
PRIORITY = 'Priority'
ISALARM = 'IsAlarm' # only new incoming alarm!
FOR_PROCESSING='4Processing'
OPERATION = "Operation"
MESSAGE_DURATION = "Message Duration" # new
PLANT = "Plant"



# == Input file(s) settings
quoteChar = "'"
delimiter = ','


# == User's settings

category_by_PCS = aeu_config["C_SOURCE"] #before it was C_TAG   
 
# json default outputTimeZone: "Etc/UTC"
#ttz = pytz.timezone(outputTimeZone)


# RAW Pcs7 Processing functions
@log_exceptions
def process_file(df,ftz):
    # ftz = pytz.timezone(ftz)
    ftz = UTC_OFFSETS[ftz]
    print(ftz)
    # only states eq to C will be processed because it means new incoming raw message
    df[FOR_PROCESSING] = df.apply(lambda row: row[STATUS] =="C" or row[STATUS] == "C hidden", axis=1)
    
    
    alarmClasses_lower = [ac.lower() for ac in alarmClasses]
    
    df[ISALARM] = (df[FOR_PROCESSING] & (df[CLASS].str.lower().str.contains('|'.join(alarmClasses_lower), case=False, regex=True)))
    
    # sets correct timezone for Accurate time(for later Li db query)
    df[TIMESTAMP] = local_to_utc(df,ftz)
    
    # sorts according to timestamps ASC
    df.sort_values(by=[TIMESTAMP], inplace=True)

    df.index.rename("index",inplace=True)

    df[TIMESTAMP] = df[TIMESTAMP].dt.tz_localize(None)
    
    # Debugging dataframe missing rows 
    # print(df[(df['Source'].str.strip() == "KV8703B/KV8703B") & (df[STATUS].str.strip() == "C")])
    
    return df

@log_exceptions
def show_pcs_statistics(df):
    # == > Statistics
    alarmCounts = len(df[(df[ISALARM] == True) & (df[FOR_PROCESSING] == True)])
    eventCount = len(df[df[FOR_PROCESSING] == True]) - alarmCounts
    dcshbCount = len(df[(df[FOR_PROCESSING] == True) & (df[SOURCE].isin(dcs_hb))])
    
    df[TIMESTAMP] = df[TIMESTAMP].dt.tz_localize(None)
    df_processing = df[df[FOR_PROCESSING] == True].sort_values(by=TIMESTAMP)
    
    report = {}
    
    report[aeu_config["SI_MODULE_NAME"]] = aeu_config["SI_MODULE_DCS_PCS7"]
    # show first & last time from processing df 
    report[aeu_config["SI_FIRST_REC"]] = df_processing.Timestamp.iat[0]
    report[aeu_config["SI_LAST_REC"]] = df_processing.Timestamp.iat[-1]
    report[aeu_config["SI_QTY_MES"]] = len(df[df[FOR_PROCESSING] == True])
    report[aeu_config["SI_QTY_AMES"]] = alarmCounts
    report[aeu_config["SI_QTY_EMES"]] = eventCount
    report[aeu_config["SI_QTY_DCS_EMES"]] = eventCount - dcshbCount
    report[aeu_config["SI_QTY_DCS_HB"]] = dcshbCount
    report[aeu_config["SI_QTY_AER_HB"]] = 0
    
    # == Alarms statistics by CATEGORY_BY
    gdf = df[(df[ISALARM] == True) & (df[FOR_PROCESSING] == True)].groupby([category_by_PCS]).count()
    gdf.rename(columns={STATUS: 'Qty'}, inplace=True)
    gdf = gdf.sort_values(['Qty', gdf.index.name], ascending=False)
    gdf = gdf['Qty']

    pgdf = gdf.reset_index()
    report[aeu_config["SI_TOPX_ALARMS"]] = pgdf.values.tolist()
    
    # == Events statistics by CATEGORY_BY
    gdf = df[(df[ISALARM] == False) & (df[FOR_PROCESSING] == True)].groupby([category_by_PCS]).count()
    gdf.rename(columns={STATUS: 'Qty'}, inplace=True)
    gdf = gdf.sort_values(['Qty', gdf.index.name], ascending=False)
    gdf = gdf['Qty']

    pgdf = gdf.reset_index()
    report[aeu_config["SI_TOPX_EVENTS"]] = pgdf.values.tolist()
    
    # Prepare report df to be stored as csv
    report_df = pd.DataFrame([report])
    report_df = report_df.map(lambda x: x.encode('unicode_escape').decode('utf-8') if isinstance(x, str) else x)
    
    # Create formatted display string
    stats_display = f"""
        First message time: {report[aeu_config["SI_FIRST_REC"]]}
        Last message time: {report[aeu_config["SI_LAST_REC"]]}
        
        Number of all messages: {df.shape[0]}
        Number of messages for processing (C): {report[aeu_config["SI_QTY_MES"]]}
        Number of alarms: {report[aeu_config["SI_QTY_AMES"]]}
        Number of events: {report[aeu_config["SI_QTY_EMES"]]}
        - thereof:
            Number of DCS events: {report[aeu_config["SI_QTY_DCS_EMES"]]}
            Number of DCS Heartbeats: {report[aeu_config["SI_QTY_DCS_HB"]]}
        """
    
    return report_df, stats_display, dcshbCount #df_processing #df is Raw Pcs7 df without tzinfo (use for saving to excel) 


# == > Prepare both pcs & linde db dataframes for CSV extraction


# == Convert processed raw AE from linde db and Pcs into csv
@log_exceptions
def prepare_xlsx(excelFile, dfLindeAeData, dfAeRawData, reportAeRawData, reportAeLindeData):
    dfStatistics = pd.DataFrame(columns=["Statistic"])
    dfStatistics.loc[len(dfStatistics.index)] = [aeu_config["SI_FIRST_REC"].replace('_', ' ')]  
    dfStatistics.loc[len(dfStatistics.index)] = [aeu_config["SI_LAST_REC"].replace('_', ' ')]
    dfStatistics.loc[len(dfStatistics.index)] = [aeu_config["SI_QTY_MES"].replace('_', ' ')]
    dfStatistics.loc[len(dfStatistics.index)] = [aeu_config["SI_QTY_AMES"].replace('_', ' ')]
    dfStatistics.loc[len(dfStatistics.index)] = [aeu_config["SI_QTY_EMES"].replace('_', ' ')]
    dfStatistics.loc[len(dfStatistics.index)] = [aeu_config["SI_QTY_DCS_EMES"].replace('_', ' ')]
    dfStatistics.loc[len(dfStatistics.index)] = [aeu_config["SI_QTY_DCS_HB"].replace('_', ' ')]
    dfStatistics.loc[len(dfStatistics.index)] = [aeu_config["SI_QTY_AER_HB"].replace('_', ' ')]
    dfStatistics.loc[len(dfStatistics.index)] = ["Total alarm difference"]
    dfStatistics.loc[len(dfStatistics.index)] = ["Total event difference"]

    dfTopXAlarms = pd.DataFrame()
    dfTopXEvents = pd.DataFrame()
    
    if reportAeRawData is not None:
        dfStatistics["Raw"] = [
            reportAeRawData[aeu_config["SI_FIRST_REC"]].iloc[0], 
            reportAeRawData[aeu_config["SI_LAST_REC"]].iloc[0],
            reportAeRawData[aeu_config["SI_QTY_MES"]].iloc[0],
            reportAeRawData[aeu_config["SI_QTY_AMES"]].iloc[0], #alarm column
            reportAeRawData[aeu_config["SI_QTY_EMES"]].iloc[0],
            reportAeRawData[aeu_config["SI_QTY_DCS_EMES"]].iloc[0],
            reportAeRawData[aeu_config["SI_QTY_DCS_HB"]].iloc[0],
            reportAeRawData[aeu_config["SI_QTY_AER_HB"]].iloc[0],   
            None, # Placeholder (Alarm difference calculated later)
            None
        ]
        # Pcs7 alarms/events report
        raw_alarms = pd.DataFrame(reportAeRawData[aeu_config["SI_TOPX_ALARMS"]].iloc[0], 
                                columns=["Tag (Raw)", "Qty (Raw)"])
        raw_events = pd.DataFrame(reportAeRawData[aeu_config["SI_TOPX_EVENTS"]].iloc[0], 
                                columns=["Tag (Raw)", "Qty (Raw)"])

    if reportAeLindeData is not None:
        dfStatistics["Linde DB"] = [
            reportAeLindeData[aeu_config["SI_FIRST_REC"]].iloc[0],  
            reportAeLindeData[aeu_config["SI_LAST_REC"]].iloc[0],
            reportAeLindeData[aeu_config["SI_QTY_MES"]].iloc[0],
            reportAeLindeData[aeu_config["SI_QTY_AMES"]].iloc[0], #alarm num
            reportAeLindeData[aeu_config["SI_QTY_EMES"]].iloc[0], #event num
            reportAeLindeData[aeu_config["SI_QTY_DCS_EMES"]].iloc[0],
            reportAeLindeData[aeu_config["SI_QTY_DCS_HB"]].iloc[0],
            reportAeLindeData[aeu_config["SI_QTY_AER_HB"]].iloc[0],
            None, # Placeholder (Alarm difference calculated later)
            None
        ]
        # AE db alarms/events report
        linde_alarms = pd.DataFrame(reportAeLindeData[aeu_config["SI_TOPX_ALARMS"]].iloc[0], 
                                  columns=["Tag (Linde DB)", "Qty (Linde DB)"])
        linde_events = pd.DataFrame(reportAeLindeData[aeu_config["SI_TOPX_EVENTS"]].iloc[0], 
                                   columns=["Tag (Linde DB)", "Qty (Linde DB)"])  
        
    # Calculate difference only if both reports exist
    if reportAeRawData is not None and reportAeLindeData is not None:
        raw_alarm_count = reportAeRawData[aeu_config["SI_QTY_AMES"]].iloc[0]
        aedb_alarm_count = reportAeLindeData[aeu_config["SI_QTY_AMES"]].iloc[0]
        raw_event_count = reportAeRawData[aeu_config["SI_QTY_EMES"]].iloc[0]
        aedb_event_count = reportAeLindeData[aeu_config["SI_QTY_EMES"]].iloc[0]
        
        # Show alarm difference
        dfStatistics.at[8, "Linde DB"] = abs(aedb_alarm_count - raw_alarm_count)
        # Show event difference
        dfStatistics.at[9, "Linde DB"] = abs(aedb_event_count - raw_event_count)
        
        
    # Merge the alarms and events data to align matching tags
    # Merge and sort alarms
    if reportAeRawData is not None and reportAeLindeData is not None:
        # Merge DataFrames (outer join to keep all tags)
        dfTopXAlarms = pd.merge(
            linde_alarms, 
            raw_alarms, 
            left_on="Tag (Linde DB)", 
            right_on="Tag (Raw)", 
            how="outer"
        )
        
        # Sort by:
        # 1. Whether tags match (matched tags first)
        # 2. Higher quantity (descending)
        dfTopXAlarms["Match"] = dfTopXAlarms["Tag (Linde DB)"] == dfTopXAlarms["Tag (Raw)"]
        dfTopXAlarms = dfTopXAlarms.sort_values(
            by=["Match", "Qty (Raw)", "Qty (Linde DB)"], 
            ascending=[True, False, False]
        ).drop(columns=["Match"])
        
        # Reorder columns for readability
        dfTopXAlarms = dfTopXAlarms[["Tag (Raw)", "Qty (Raw)", "Tag (Linde DB)", "Qty (Linde DB)"]]
        
        # Do the same for events
        dfTopXEvents = pd.merge(
            linde_events, 
            raw_events, 
            left_on="Tag (Linde DB)", 
            right_on="Tag (Raw)", 
            how="outer"
        )
        dfTopXEvents["Match"] = dfTopXEvents["Tag (Linde DB)"] == dfTopXEvents["Tag (Raw)"]
        dfTopXEvents = dfTopXEvents.sort_values(
            by=["Match", "Qty (Raw)", "Qty (Linde DB)"], 
            ascending=[True, False, False]
        ).drop(columns=["Match"])
        dfTopXEvents = dfTopXEvents[["Tag (Raw)", "Qty (Raw)", "Tag (Linde DB)", "Qty (Linde DB)"]]
        
        
        # After reordering Tags based on same name, do the Quantity difference calculation
        
        # Calculate percentage difference for TopX Alarms
        dfTopXAlarms['% Difference'] = ((dfTopXAlarms['Qty (Raw)'] - dfTopXAlarms['Qty (Linde DB)']) / 
                                      dfTopXAlarms['Qty (Linde DB)']) * 100
        dfTopXAlarms['% Difference'] = dfTopXAlarms['% Difference'].apply(lambda x: f"{x:.2f}%")
        # Calculate percentage difference
        dfTopXEvents['% Difference'] = ((dfTopXEvents['Qty (Raw)'] - dfTopXEvents['Qty (Linde DB)']) / 
                                      dfTopXEvents['Qty (Linde DB)']) * 100
        dfTopXEvents['% Difference'] = dfTopXEvents['% Difference'].apply(lambda x: f"{x:.2f}%")
        
    try:
        # == Saves to Excel file
        output_path = os.path.join("Output", excelFile)
        logger.info(f"Saving to '{output_path}'...")
        with pd.ExcelWriter("./Output/" + excelFile, mode='w', engine='xlsxwriter', datetime_format='YYYY-MM-DD HH:MM:SS.000', date_format='YYYY-MM-DD') as writer: 
            if dfAeRawData is not None:
                dfAeRawData.to_excel(writer, sheet_name='AeRawData')   
                (max_row, max_col) = dfAeRawData.shape
                worksheet = writer.sheets["AeRawData"]
                worksheet.autofilter(0, 0, max_row, max_col - 1)
                worksheet.autofit()
                worksheet.freeze_panes(1, 0) 
            
            if dfLindeAeData is not None:
                dfLindeAeData.to_excel(writer, sheet_name='AeLindeData')
                (max_row, max_col) = dfLindeAeData.shape
                worksheet = writer.sheets["AeLindeData"]
                worksheet.autofilter(0, 0, max_row, max_col - 1)
                worksheet.autofit()
                worksheet.freeze_panes(1, 0)

            if dfStatistics is not None:
                dfStatistics.to_excel(writer, sheet_name='Statistics')
                (max_row, max_col) = dfStatistics.shape
                worksheet = writer.sheets["Statistics"]    
                worksheet.autofit()
                worksheet.freeze_panes(1, 0)
            
            if dfTopXAlarms is not None:
                dfTopXAlarms.to_excel(writer, sheet_name='TopX Alarms')
                (max_row, max_col) = dfTopXAlarms.shape
                worksheet = writer.sheets["TopX Alarms"]
                worksheet.autofilter(0, 0, max_row, max_col)
                worksheet.autofit()
                worksheet.freeze_panes(1, 0)
            
            if dfTopXEvents is not None:
                dfTopXEvents.to_excel(writer, sheet_name='TopX Events')
                (max_row, max_col) = dfTopXEvents.shape
                worksheet = writer.sheets["TopX Events"]
                worksheet.autofilter(0, 0, max_row, max_col)
                worksheet.autofit()
                worksheet.freeze_panes(1, 0)   
        return (f"Successfully saved {excelFile} to Output folder.", True)
    except Exception as e:
        logger.error(f"Saving to Excel failed: {e}")
        return (f"Saving to Excel failed: {e}", False)


class DataValidationTool(ctk.CTk):
    def __init__(self):
        try:
            super().__init__()
            logger.info("Initializing DataValidationTool")

            # Configure appearance
            ctk.set_appearance_mode("Light")
            ctk.set_default_color_theme("blue")

            self.config_version = loadConfiguration()["version"]
            self.config_colors = loadConfiguration()["colors"]
            self.config_window = loadConfiguration()["window"]
            
            # Configure window
            self.title("PCS7 AE Data Validation Tool")
            self.geometry("1000x870")  # Wider to accommodate sidebar
            self.minsize(1000, 600)  # Minimum window size to ensure readability
            self.protocol("WM_DELETE_WINDOW", self.on_closing)
            
            # Disable maximize button (Windows)
            self.attributes('-toolwindow', self.config_window)  # This removes maximize/minimize buttons on Windows
            
            # Initialize variables
            self.allMessages = []
            self.report = {}
            self.current_df = None
            self.config = None
            self.from_time = None
            self.to_time = None
            self.df_journal = None
            self.df_operation = None
            self.journal_file_key = None
            self.missing_columns = []
            
            # Main columns used for allarm counting etc
            self.colNames = [TIMESTAMP,SOURCE,CLASS,TYPE,STATUS] 

            # Configure window grid to expand
            self.grid_rowconfigure(0, weight=1)
            self.grid_columnconfigure(0, weight=0)  # Sidebar (fixed width)
            self.grid_columnconfigure(1, weight=1)  # Main content (expandable)

            # Create sidebar frame
            self.sidebar_frame = ctk.CTkFrame(self, width=240)
            self.sidebar_frame.grid(row=0, column=0, sticky="nsew")
            self.sidebar_frame.grid_propagate(False)  # Prevent the frame from shrinking

            # Create main content frame
            self.main_content_frame = ctk.CTkFrame(self)
            self.main_content_frame.grid(row=0, column=1, sticky="nsew")
            
            # Configure rows in main_content_frame - add row for footer
            self.main_content_frame.grid_rowconfigure(0, weight=1)  # Content area
            self.main_content_frame.grid_rowconfigure(1, weight=0)  # Footer area
            self.main_content_frame.grid_columnconfigure(0, weight=1)

            # Scrollable frame for main content
            self.scrollable_frame = ctk.CTkScrollableFrame(self.main_content_frame, width=730, height=800)
            self.scrollable_frame.grid(row=0, column=0, padx=20, pady=20, sticky="nsew")
            self.scrollable_frame.grid_columnconfigure(0, weight=1)

            # Create GUI elements
            self.create_widgets()
            self.create_sidebar()
            self._create_footer_description()  # Create footer separately outside the scrollable area
            self.stats_ae_textbox.configure(state="disabled")
            self.stats_textbox.configure(state="disabled")
            logger.info("LindeDataValidationTool initialization complete")
        except Exception as e:
            logger.critical(f"Failed to initialize LindeDataValidationTool: {str(e)}")
            logger.critical(traceback.format_exc())
            raise
        
    def _create_button(self, parent, text, command, fg_color=None, **kwargs):
        defaults = {
            "width": 200,
            "height": 40,
            "border_color": "black",
            "fg_color": "white", #fg_color or self.config_colors["BUTTON_COL"],
            "text_color": "black" #if fg_color == "white" else None,
        }
        defaults.update(kwargs)
        return ctk.CTkButton(parent, text=text, command=command, **defaults)

    def create_sidebar(self):
        """Create sidebar with import functionality."""
        # Add logo to the top of sidebar
        self.sidebar_logo = ctk.CTkImage(light_image=Image.open("img/linde_logo.jpg"), size=(200, 100))
        self.sidebar_logo_label = ctk.CTkLabel(self.sidebar_frame, image=self.sidebar_logo, text="")
        self.sidebar_logo_label.grid(row=0, column=0, pady=(20, 20), padx=10)
        
        # First Row: Timezone Selection
        timezone_frame = ctk.CTkFrame(self.sidebar_frame)
        timezone_frame.grid(row=1, column=0, rowspan=2, pady=(15,10), padx=10, sticky="w")
        timezone_frame.grid_columnconfigure(1, weight=1)
        
        # Timezone Label
        timezone_label = ctk.CTkLabel(timezone_frame, text="1. Select timezone:", font=("Arial", 18, "bold"))
        timezone_label.grid(row=0, column=0, sticky="w", padx=(10,10), pady=10)
        
        # Timezone Dropdown
        self.timezone_combobox = ctk.CTkComboBox(timezone_frame, 
                                            #values=pytz.common_timezones,
                                            values=list(UTC_OFFSETS.keys()),
                                            width=210,
                                            height=35)
        self.timezone_combobox.grid(row=1, column=0, sticky="w", padx=(0,10), pady=10)
        CTkScrollableDropdown(self.timezone_combobox, values=list(UTC_OFFSETS.keys()),autocomplete=True) 
        # Set default timezone
        self.timezone_combobox.set(defaultTimeZone)

        # Import section header
        self.sidebar_import_label = ctk.CTkLabel(self.sidebar_frame, 
                                 text="2. Import files", 
                                 font=("Arial", 18, "bold"))
        self.sidebar_import_label.grid(row=3, column=0, sticky="w", padx=10, pady=(10, 15))
        
        # Journal import section
        self.sidebar_journal_header = ctk.CTkLabel(self.sidebar_frame, 
                                 text="Import a journal list", 
                                 font=("Arial", 14, "bold"))
        self.sidebar_journal_header.grid(row=4, column=0, sticky="w", padx=20, pady=(5, 5))
        
        self.load_pcs_button = self._create_button(self.sidebar_frame,"Load file",self.handle_journal_load)
        self.load_pcs_button.grid(row=5, column=0, sticky="w", padx=20, pady=(5, 15))
        
        self.status_label_journal = ctk.CTkLabel(self.sidebar_frame, text="No files loaded", font=("Arial", 14))   
        self.status_label_journal.grid(row=6, column=0, padx=10, pady=(0,5), sticky="w")
        
        # Operation import section
        self.sidebar_operation_header = ctk.CTkLabel(self.sidebar_frame, 
                                 text="Import an operation list", 
                                 font=("Arial", 14, "bold"))
        self.sidebar_operation_header.grid(row=7, column=0, sticky="w", padx=20, pady=(5, 5))
        
        self.load_operation_button = self._create_button(self.sidebar_frame,"Load file",self.handle_operation_load)
        self.load_operation_button.grid(row=8, column=0, sticky="w", padx=20, pady=(5, 15))
        
        self.status_label_operation = ctk.CTkLabel(self.sidebar_frame, text="No files loaded", font=("Arial", 14))    
        self.status_label_operation.grid(row=9, column=0, padx=10, pady=(0,5), sticky="w")
        
        # addition, if user wants to process just one loaded file (Journallist)
        self.apply_loaded_file = ctk.CTkButton(self.sidebar_frame, 
                                       text="Apply", 
                                       fg_color=self.config_colors["BUTTON_COL"],
                                       command=self.handle_onefile_load,
                                       width=150,
                                       height=40)
        self.apply_loaded_file.grid(row=10, column=0, sticky="w", padx=20, pady=(5, 15))

    def create_widgets(self):
        """Create and arrange all GUI elements."""
        self._create_file_selection_section()
        self._create_linde_ae_database_section()
        self._create_excel_export_section()
    
        

    def _create_file_selection_section(self):
        """Create file selection components with improved layout."""
        # Main File Selection Frame
        self.file_selection_frame = ctk.CTkFrame(self.scrollable_frame)
        self.file_selection_frame.grid(row=0, column=0, sticky="ew", pady=10)
        self.file_selection_frame.grid_columnconfigure(1, weight=1)

        # Fourth Row: Status Labels (now in a separate row)
        status_frame = ctk.CTkFrame(self.file_selection_frame)
        status_frame.grid(row=0, column=0, columnspan=3, pady=(0, 10), padx=10, sticky="ew")
        status_frame.grid_columnconfigure(0, weight=1)

        # Combined Status Label - main status label
        self.status_label = ctk.CTkLabel(status_frame, text="No files processed", font=("Arial", 14))    
        self.status_label.grid(row=0, column=0, padx=10, pady=(0,5), sticky="new")

        # Hidden operation status label (not visible but kept for compatibility)
        self.operation_status_label = ctk.CTkLabel(status_frame, text="")

        # Fifth Row: Two Scrollable Frames for Journal and Operation DataFrames
        scrollable_frames_row = ctk.CTkFrame(self.file_selection_frame)
        scrollable_frames_row.grid(row=1, column=0, columnspan=3, pady=(5, 10), padx=10, sticky="nsew")
        scrollable_frames_row.grid_columnconfigure(0, weight=1)  # First scrollable frame column
        scrollable_frames_row.grid_columnconfigure(1, weight=1)  # Second scrollable frame column
        scrollable_frames_row.grid_rowconfigure(1, weight=1)  # Allow row to expand vertically

        # Add a label at the top of the frame
        map_columns_label = ctk.CTkLabel(scrollable_frames_row, text="3. Map correct column names", font=("Arial", 18, "bold"))
        map_columns_label.grid(row=0, column=0, columnspan=2, pady=0, sticky="w")

        # First Scrollable Frame: Journal DataFrame
        self.processed_columns_frame = ctk.CTkScrollableFrame(scrollable_frames_row, label_text="Imported files columns")
        self.processed_columns_frame.grid(row=1, column=0, padx=(0, 5), pady=5, sticky="nsew")

        # Second Scrollable Frame: Operation DataFrame
        self.calculation_columns_frame = ctk.CTkScrollableFrame(scrollable_frames_row, label_text="Columns for calculations")
        self.calculation_columns_frame.grid(row=1, column=1, padx=(5, 0), pady=5, sticky="nsew")

        # Button to save new column names
        self.change_columns_button = ctk.CTkButton(
            scrollable_frames_row,
            text="Process loaded files",
            fg_color=self.config_colors["BUTTON_COL"],
            command=self.set_renamed_columns,
            height=30
        )
        self.change_columns_button.grid(row=2, column=0, columnspan=2, padx=10, pady=(10, 0), sticky="ew")


        # Sixth Row: Summary Section
        summary_frame = ctk.CTkFrame(self.file_selection_frame)
        summary_frame.grid(row=2, column=0, columnspan=3, pady=(5, 10), padx=10, sticky="ew")
        summary_frame.grid_columnconfigure(0, weight=1)

        # Summary Label
        self.pcs_summary_label = ctk.CTkLabel(summary_frame, text="Summary:", font=("Arial", 14, "bold"))
        self.pcs_summary_label.grid(row=0, column=0, padx=(10, 0), pady=(10, 5), sticky="w")

        # Statistics text box
        self.stats_textbox = ctk.CTkTextbox(summary_frame, height=180)
        self.stats_textbox.grid(row=1, column=0, sticky="ew", padx=10, pady=(0, 10))
    
    def _create_linde_ae_database_section(self):
        """Create plant entry components."""
        # Label
        self.label = ctk.CTkLabel(self.scrollable_frame, 
                                text="4. Import data from Linde AE database", 
                                font=("Arial", 21, "bold"))
        self.label.grid(row=2, column=0, sticky="w", pady=(0,10), padx=(0,10))

        # Plant Entry Frame
        self.plant_entry_frame = ctk.CTkFrame(self.scrollable_frame)
        self.plant_entry_frame.grid(row=3, column=0, sticky="ew", pady=10, padx=10)
        self.plant_entry_frame.grid_columnconfigure(1, weight=1)
        self.plant_entry_frame.grid_columnconfigure(2, weight=1)

        # Plant Name Label
        self.plant_label = ctk.CTkLabel(self.plant_entry_frame, text="Plant name:", font=("Arial", 14, "bold"))
        self.plant_label.grid(row=0, column=0, sticky="w", padx=(0,5),pady=(10,0))

        # Plant Entry
        self.plant_entry = ctk.CTkEntry(self.plant_entry_frame, 
                                        placeholder_text="Enter correct plant name", 
                                        width=160, height=40
                                        )
        self.plant_entry.grid(row=0, column=1, sticky="wn", padx=(0,0),pady=(10,0))

        # Load AE db button
        self.load_aedb_button = ctk.CTkButton(self.plant_entry_frame, 
                                            text="Load data", 
                                            fg_color=self.config_colors["BUTTON_COL"],
                                            command=self.handle_plant_entry,
                                            width=100,
                                            height=40)
        self.load_aedb_button.grid(row=0, column=1,sticky="en",padx=(0,140),pady=(10,0))
        
        # Error Label
        self.plant_error_label = ctk.CTkLabel(self.plant_entry_frame, 
                                            text="", 
                                            text_color="red")
        self.plant_error_label.grid(row=1, column=0, columnspan=3, sticky="w")
        
        # Status label
        self.pcs_summary_label = ctk.CTkLabel(self.plant_entry_frame, text="Summary:",font=("Arial",14,"bold"))
        self.pcs_summary_label.grid(row=2, column=0, padx=0, sticky="w")
        
        # Linde AE database textbox
        self.stats_ae_textbox = ctk.CTkTextbox(self.plant_entry_frame, height=180)
        self.stats_ae_textbox.grid(row=3, column=0,columnspan=3, sticky="ew", padx=0)
        
    def _create_excel_export_section(self):
        """Create Excel export components."""
        # Heading label
        self.excel_label = ctk.CTkLabel(self.scrollable_frame, 
                                text="5. Save data to Excel workbook", 
                                font=("Arial", 21, "bold"))
        self.excel_label.grid(row=4, column=0, sticky="w", pady=10, padx=(0,10))
        
        # Excel Export Frame
        self.excel_frame = ctk.CTkFrame(self.scrollable_frame)
        self.excel_frame.grid(row=5, column=0, sticky="ew", pady=(10,0), padx=10)
        self.excel_frame.grid_columnconfigure(1, weight=1)
        self.excel_frame.grid_columnconfigure(2, weight=1)

        
        # Plant Name Label
        self.excel_plant_label = ctk.CTkLabel(self.excel_frame, text="File name:", font=("Arial", 14, "bold"))
        self.excel_plant_label.grid(row=0, column=0, sticky="w", padx=(0,10),pady=(10,0))
        
        # Excel Entry
        self.excel_entry = ctk.CTkEntry(self.excel_frame, 
                                        placeholder_text='Insert filename', 
                                        width=160,height=40)
        self.excel_entry.grid(row=0, column=1, sticky="wn", padx=(0,5),pady=(10,0))

        # Excel Save Button
        self.to_excel_button = ctk.CTkButton(self.excel_frame, 
                                             text="Save data", 
                                             fg_color=self.config_colors["BUTTON_COL"],
                                             command=self.handle_excel_saving,
                                             width=100,height=40)
        self.to_excel_button.grid(row=0, column=1, padx=(0,140),pady=(10,0),sticky="en")

        # Excel Error Label
        self.excel_error_label = ctk.CTkLabel(self.excel_frame, text="")
        self.excel_error_label.grid(row=1, column=0,columnspan=3, sticky="w")
        
    # Footer    
    def _create_footer_description(self):
        self.footer_frame = ctk.CTkFrame(self.main_content_frame)
        self.footer_frame.grid(row=1, column=0, sticky="ew", padx=20, pady=(0, 10))

        # Configure columns to distribute space evenly
        self.footer_frame.grid_columnconfigure(0, weight=1)
        self.footer_frame.grid_columnconfigure(1, weight=1)
        self.footer_frame.grid_columnconfigure(2, weight=1)

        self.version_label = ctk.CTkLabel(self.footer_frame, text=f"Version: {self.config_version}", font=("Arial", 12))
        self.version_label.grid(row=0, column=0, sticky="w", padx=10, pady=5)

        self.description_label = ctk.CTkLabel(self.footer_frame, text="Description: REE ROC, Linde Gas a.s. 2025", font=("Arial", 12))
        self.description_label.grid(row=0, column=1, sticky="ew", padx=10, pady=5)

        self.support_label = ctk.CTkLabel(self.footer_frame, text="Support: michal.vitos@linde.com", font=("Arial", 12))
        self.support_label.grid(row=0, column=2, sticky="e", padx=10, pady=5)
    
    
    # 1. ======== Load CSV files from UI WINDOW =========
    
    def load_journal_csv(self):
        """Load journal CSV file and return file name and dataframe."""
        file_path = filedialog.askopenfilename(
            filetypes=[("CSV files", ".csv"), ("All files", "*.*")]
        )   
        if not file_path:
            return None, None
        
        filename = os.path.basename(file_path)
        file_key = os.path.splitext(filename)[0]
        
        try:
            # Read with case-insensitive date column handling
            df = pd.read_csv(file_path, sep=';', encoding="utf-16")
            
            # Find date/time columns
            date_col = next(col for col in df.columns if col.lower() == 'date')
            time_col = next(col for col in df.columns if col.lower() == 'time')
            
            # Parse datetime
            df['Timestamp'] = pd.to_datetime(
                df[date_col] + ' ' + df[time_col],
                dayfirst=True,
                errors='coerce'
            )
            df.drop([date_col, time_col], axis=1, inplace=True)
            df.sort_values(by='Timestamp', inplace=True)
            
            # Reset UI state
            self.df_operation = None
            self.missing_columns = []
            self.status_label_operation.configure(text="No file loaded", text_color="red")
            self.status_label.configure(text="")
            self._clear_textboxes()
            
            self.status_label_journal.configure(
                text=f"Loaded: {filename}",
                text_color=self.config_colors["SUCCES_COL"]
            )
            return file_key, df
            
        except Exception as e:
            self.status_label_journal.configure(
                text=f"Error: {str(e)[:50]}...",
                text_color="red"
            )
            logger.error(f"Journal CSV error: {str(e)}", exc_info=True)
            return None, None
    
    def _clear_textboxes(self):
        """Clear all textboxes in the UI."""
        self.stats_textbox.configure(state="normal")
        self.stats_textbox.delete("1.0", "end")
        self.stats_ae_textbox.configure(state="normal")
        self.stats_ae_textbox.delete("1.0", "end")
        
    def load_operation_csv(self):
        """Load operation CSV file and return dataframe."""
        operation_file_path = filedialog.askopenfilename(
            title="Select Operation List File",
            filetypes=[("CSV files", ".csv"), ("All files", "*.*")]
        )   
        if not operation_file_path:
            return None
        
        try:
            # Update status label
            filename = os.path.basename(operation_file_path)
            self.operation_status_label.configure(
                text=f"Filename: {filename}",
                text_color=self.config_colors["SUCCES_COL"]
            )
            file_key = os.path.splitext(filename)[0]  # Remove .csv extension  
            
            # Debug: Log file loading attempt
            logger.debug(f"Attempting to load file: {operation_file_path}")
            
            # Read the CSV file first without parsing dates
            df_operation = pd.read_csv(
                operation_file_path,
                sep=';',
                encoding="utf-16"
            )
            
            # Debug: Log columns found
            logger.debug(f"Columns found: {list(df_operation.columns)}")
            
            try:
                # Find date/time columns regardless of case
                date_col = next(col for col in df_operation.columns if col.lower() == 'date')
                time_col = next(col for col in df_operation.columns if col.lower() == 'time')
            except StopIteration:
                raise ValueError("Could not find both 'Date' and 'Time' columns in the CSV file")
            
            # Debug: Log found datetime columns
            # logger.debug(f"Using date column: '{date_col}', time column: '{time_col}'")
            
            # Parse the dates with error handling
            try:
                df_operation['Timestamp'] = pd.to_datetime(
                    df_operation[date_col] + ' ' + df_operation[time_col],
                    dayfirst=True,
                    errors='coerce'  # Convert parsing errors to NaT instead of failing
                )
                
                # Check for failed date parsing
                if df_operation['Timestamp'].isna().any():
                    na_count = df_operation['Timestamp'].isna().sum()
                    logger.warning(f"{na_count} rows could not be parsed as dates")
            except Exception as e:
                raise ValueError(f"Failed to parse dates: {str(e)}")
            
            # Drop the original date/time columns
            df_operation.drop([date_col, time_col], axis=1, inplace=True)
            
            # Debug: Log sample timestamps
            # logger.debug(f"Sample timestamps: {df_operation['Timestamp'].head(3)}")
            
            # Sort by timestamp
            df_operation.sort_values(by='Timestamp', inplace=True)
            
            logger.info(f"Successfully loaded operation CSV with {len(df_operation)} rows")
            self.status_label_operation.configure(
                text=f"Loaded: {file_key}",
                text_color=self.config_colors["SUCCES_COL"]
            )
            return file_key, df_operation
            
        except Exception as e:
            error_msg = f"Failed to load operation list: {str(e)}"
            logger.error(error_msg, exc_info=True)  # Include stack trace
            self.status_label_operation.configure(
                text=error_msg[:50] + "..." if len(error_msg) > 50 else error_msg,
                text_color="red"
            )
            return None

    
    ## 2. Joining raw journal+operation on timeintersection
        
    # Load file - Button command handlers to separate loading from processing
    def handle_journal_load(self):
        """Handler for loading journal files only."""
        self.journal_file_key, self.df_journal = self.load_journal_csv()
        self.df_operation = None
        self.apply_loaded_file.configure(text=f"Load only {self.journal_file_key}")

    def handle_operation_load(self):
        """Handler for loading operation files only."""
        self.operation_file_key, self.df_operation = self.load_operation_csv()
        # Change apply button title based of loaded file
        self.apply_loaded_file.configure(text=f"Load only {self.operation_file_key}")
        
        # join both journal&operation on timeintersection
        if self.df_journal is not None:
            # Change apply button title based of loaded file
            self.apply_loaded_file.configure(text=f"Apply")
            self.join_journal_operation_raw() 
    
    
    def handle_onefile_load(self):
        # Check if both files are loaded
        if hasattr(self, 'df_operation') and self.df_operation is not None and hasattr(self, 'df_journal') and self.df_journal is not None:
            self.status_label.configure(text=f"Both: {self.journal_file_key} + {self.operation_file_key} selected", text_color=self.config_colors["SUCCES_COL"])
            self.join_journal_operation_raw()
            
        # If only journal is loaded
        elif hasattr(self, 'df_journal') and self.df_journal is not None:
            self.status_label.configure(text=f"Selected only: {self.journal_file_key}", text_color=self.config_colors["SUCCES_COL"])
            self.combined_df = self.df_journal
            
            # Define calculation columns and show together with loaded CSV to compare inside UI 
            self._populate_scrollable_frame(self.processed_columns_frame, self.combined_df.columns)
            self._populate_scrollable_frame(self.calculation_columns_frame, self.colNames)
            
        # If only operation is loaded    
        elif hasattr(self, 'df_operation') and self.df_operation is not None:
            self.status_label.configure(text=f"Selected only: {self.operation_file_key}", text_color=self.config_colors["SUCCES_COL"])
            self.combined_df = self.df_operation
        
            # Define calculation columns and show together with loaded CSV to compare inside UI 
            self._populate_scrollable_frame(self.processed_columns_frame, self.combined_df.columns)
            self._populate_scrollable_frame(self.calculation_columns_frame, self.colNames)
            

    def join_journal_operation_raw(self):
        # Skip if no journal data is loaded
        if not hasattr(self, 'df_journal') or self.df_journal is None:
            return
        else:
            df_journal = self.df_journal.copy()
        if not hasattr(self, 'df_operation') or self.df_operation is None:
            return
        else:
            df_operation = self.df_operation.copy()

        try:
            # Najdi průnik časového intervalu (podle minut)
            start = max(df_journal[TIMESTAMP].dt.floor('min').min(), df_operation[TIMESTAMP].dt.floor('min').min())
            end = min(df_journal[TIMESTAMP].dt.floor('min').max(), df_operation[TIMESTAMP].dt.floor('min').max())

            # Filtrování na základě průniku
            df1_common = df_journal[(df_journal[TIMESTAMP].dt.floor('min') >= start) & (df_journal[TIMESTAMP].dt.floor('min') <= end)]
            df2_common = df_operation[(df_operation[TIMESTAMP].dt.floor('min') >= start) & (df_operation[TIMESTAMP].dt.floor('min') <= end)]

            # Sloučení pod sebou
            self.combined_df = pd.concat([df1_common, df2_common], ignore_index=True).sort_values(by=TIMESTAMP)
            if self.combined_df.empty:
                self.status_label.configure(text=f"Warning! No time intersection  {self.journal_file_key} and {self.operation_file_key}",text_color="red")
            # Journal&Operational lists should match this defined column structure - User should change imported df columns based of this
           
            #main classes that could be used for processing and will be displayed
            
            self._populate_scrollable_frame(self.processed_columns_frame, self.combined_df.columns)
            self._populate_scrollable_frame(self.calculation_columns_frame, self.colNames)
            
        except Exception as e:
            logger.error(f"Error in join_journal_operation_raw: {str(e)}")
            logger.error(traceback.format_exc())
            self.status_label_journal.configure(text=f"Error: {str(e)}", text_color="red")   
            self.status_label_operation.configure(text=f"Error: {str(e)}", text_color="red")   
        
        
        
        
    
    def _populate_scrollable_frame(self, frame, columns):
        """Populate a scrollable frame with checkboxes and rename entries for column names."""
        # Clear existing widgets in the frame
        for widget in frame.winfo_children():
            widget.destroy()

        # Define standard columns with their descriptions
        standard_columns = {
            TIMESTAMP: "Time of record",
            SOURCE: "HEARTBEAT identifier",
            CLASS: "Alarm identifier",
            TYPE: "if Class missing",
            STATUS: "Coming message identifier"
        }
        
        # Check for missing standard columns
        missing_columns = [col for col in standard_columns if col not in columns]
        # This could happen only when columns for processing are imported
        if missing_columns:
            self.status_label.configure(text=f"Columns for calculation missing: {missing_columns}",text_color="red")
            
            self.missing_columns = missing_columns
            
        # Add checkboxes and rename entries for each column  
        for i, column in enumerate(columns):
            # Check if the column name matches any in colNames case-insensitively but not case-sensitively
            if column.upper() in [name.upper() for name in standard_columns] and column not in standard_columns:
                # If the column name matches but the case is different, color the label
                label = ctk.CTkLabel(frame, text=column, text_color="red")  # Use red color for emphasis
                self.status_label.configure(text=f"Case sensitivity issue in: {column}", text_color="red")
            else:
                # Otherwise, use the default color
                if column.upper() not in [column_miss.upper() for column_miss in self.missing_columns]:
                    label = ctk.CTkLabel(frame, text=column)
                else:
                    label=ctk.CTkLabel(frame, text=column,text_color="red")

            label.grid(row=i, column=0, padx=10, pady=5, sticky="w")

            if frame == self.processed_columns_frame:
                # Entry for renaming the column
                rename_entry = ctk.CTkEntry(frame, placeholder_text=f"Rename: {column}")
                rename_entry.grid(row=i, column=1, padx=10, pady=5, sticky="ew")
                
            if frame == self.calculation_columns_frame:
                description = standard_columns.get(column)
                describe_label = ctk.CTkLabel(frame, text=description)
                describe_label.grid(row=i, column=1, padx=10, pady=5, sticky="ew")
            
        
        




    def get_renamed_columns(self, frame):
        """Retrieve the renamed columns from a scrollable frame."""
        renamed_columns = {}
        for i, (checkbox, rename_entry) in enumerate(zip(frame.winfo_children()[::2], frame.winfo_children()[1::2])):
            original_name = checkbox.cget("text")
            new_name = rename_entry.get().strip()
            renamed_columns[original_name] = new_name if new_name else original_name
        return renamed_columns
    
    
    # Process loaded files - Button command handler
    def set_renamed_columns(self):
        """
        This function proceeds after timeintersection(join_journal_operation_raw), when 'Process loaded files' is pressed
        Process the data after renaming columns."""
        # Retrieve renamed columns for both frames
        renamed_combined_columns = self.get_renamed_columns(self.processed_columns_frame)
        
        # Rename columns in the combined journal & operation dataframe with time intersection data
        if self.combined_df is not None:
            self.combined_df.rename(columns=renamed_combined_columns, inplace=True)
        try:
            # After time intersection of combined data, process them together to convert time into User defined timezone & add columns for statistics
            self.raw_pcs_df = process_file(self.combined_df,self.timezone_combobox.get())
            self.update_pcs_summary(self.raw_pcs_df.copy())
        except Exception as e:
            logger.error(f"Error in set_renamed_columns: {str(e)}")
            logger.error(traceback.format_exc())
            self.status_label.configure(text=f"Error: {str(e)}", text_color="red")

    
    # Uses process_file ouput for counting and alarms etc.
    def update_pcs_summary(self,raw_pcs_df):
        # Generate statistics
        
        # df_journal = self.df_journal.copy()
        # df_operation = self.df_operation.copy()
        self.raw_pcs_df = raw_pcs_df.copy()
        self.pcs_report, stats_text, self.dcshbCount = show_pcs_statistics(self.raw_pcs_df) # changed this to self.raw_pcs_df from raw_pcs_df.copy()
        self.sorted_pcs_df = self.raw_pcs_df[self.raw_pcs_df[FOR_PROCESSING] == True].sort_values(by=TIMESTAMP)
        
        # Update UI with details about the filtering
        if hasattr(self, 'combined_df') and self.combined_df is not None and hasattr(self, 'df_operation') and self.df_operation is not None and hasattr(self, 'df_journal') and self.df_journal is not None:
            status_text = f"Filename: {self.journal_file_key}: {len(self.df_journal)} rows | "+\
                f"Filename: {self.operation_file_key}: {len(self.df_operation)} rows | "+\
                    f"\n Combined files (time intersection): {len(self.combined_df)}"
        elif hasattr(self, 'df_journal') and self.df_journal is not None:
            status_text = f"Filename: {self.journal_file_key}: {len(self.df_journal)} rows"
        elif hasattr(self, 'df_operation') and self.df_operation is not None:
            status_text = f"Filename: {self.operation_file_key}: {len(self.df_operation)} rows"
        
            
        
        self.status_label.configure(text=status_text, text_color=self.config_colors["SUCCES_COL"])
        
        # Update stats display
        self.stats_textbox.configure(state="normal")
        self.stats_textbox.delete("1.0", "end")
        self.stats_textbox.insert("1.0", stats_text)
        self.stats_textbox.configure(state="disabled")
        
        # Store time range
        if not self.sorted_pcs_df.empty:
            self.fromTime = self.sorted_pcs_df[TIMESTAMP].iat[0]
            self.toTime = self.sorted_pcs_df[TIMESTAMP].iat[-1]
        
        # Enable the plant entry
        self.plant_entry.configure(state="normal")
        self.plant_entry.focus()
        
                
    # == > AE from Linde DB 
    def handle_plant_entry(self, event=None):
        if not hasattr(self, 'config') or not self.config:
            self.config = loadConfiguration()
        
        plant_name = self.plant_entry.get()
        self.plant_name = plant_name
        
        if not plant_name:
            self.plant_error_label.configure(text="Please enter a plant name")
            return
            
        try:
            df_raw,hint_message = loadData(
                plant_name,
                self.fromTime,
                self.toTime,
                self.config["aedb"]["server"],
                self.config["aedb"]["port"],
                self.config["aedb"]["db"],
                isDebug=False
            )
            
            if len(df_raw) == 0 and not hint_message:
                self.plant_error_label.configure(text="No data found for this plant name")
                
            elif hint_message:
                self.plant_error_label.configure(text=hint_message)
            
            else:
                self.plant_error_label.configure(text="Data loaded successfully!",text_color=self.config_colors["SUCCES_COL"])
                self.plant_entry.configure(state="disabled")  # Disable entry
                
                # Process the data
                self.ae_df = transfer_aereporting_df(df_raw.copy(),self.timezone_combobox.get())
                self.ae_report, stats_str, self.ae_dcshbCount = show_ae_statistics(self.ae_df.copy())
                # Update the stats_ae_textbox with the results
                self.stats_ae_textbox.configure(state="normal")
                self.stats_ae_textbox.delete("1.0", "end")
                self.stats_ae_textbox.insert("1.0", f"{stats_str}")
                self.stats_ae_textbox.configure(state="disabled")
                
        except Exception as e:
            self.plant_error_label.configure(text=f"Error: {str(e)}")
            logger.error(f"Error handling plant entry: {e}")
            
            
    def clear_plant_entry(self):
        self.plant_entry.configure(state="normal")  # Re-enable entry
        self.plant_entry.delete(0, "end")  # Clear the entry
        self.plant_error_label.configure(text="")  # Clear error message
        self.plant_entry.focus()  # Set focus to entry
            
    def handle_excel_saving(self):
        excel_file = self.excel_entry.get()
        if not excel_file:
            self.excel_error_label.configure(text="Please enter a file name")
            return
        
        try:
            # Check if all required dataframes and reports exist
            if not hasattr(self, 'ae_df') or self.ae_df is None:
                self.excel_error_label.configure(text="Error: AE DataFrame not loaded",text_color=self.config_colors["ERROR_COL"])
                return
                
            if not hasattr(self, 'raw_pcs_df') or self.raw_pcs_df is None:
                self.excel_error_label.configure(text="Error: PCS DataFrame not loaded",text_color=self.config_colors["ERROR_COL"])
                return
                
            if not hasattr(self, 'pcs_report') or self.pcs_report is None:
                self.excel_error_label.configure(text="Error: PCS report not generated",text_color=self.config_colors["ERROR_COL"])
                return
                
            if not hasattr(self, 'ae_report') or self.ae_report is None:
                self.excel_error_label.configure(text="Error: AE report not generated",text_color=self.config_colors["ERROR_COL"])
                return
            
            # Add .xlsx extension if not already present
            if not excel_file.endswith('.xlsx'):
                excel_file += '.xlsx'
                
            # Now call prepare_xlsx with detailed error tracking
            if self.plant_name:
                # reordering columns
                # colNames = [TIMESTAMP,STATUS, SOURCE,CLASS,TYPE,EVENT,ISALARM,PRIORITY,AREA,MESSAGE_DURATION,PLANT,NUMBER, FOR_PROCESSING]   # dont use cuz plants can miss some columns
                self.raw_pcs_df[PLANT] = self.plant_name
                # self.pcs_df = self.pcs_df.loc[:,colNames]
            
            statement,succes = prepare_xlsx(excel_file, self.ae_df, self.raw_pcs_df, self.pcs_report, self.ae_report)
            if succes:
                self.excel_error_label.configure(text=statement, text_color=self.config_colors["SUCCES_COL"])
            else:
                self.excel_error_label.configure(text=statement, text_color=self.config_colors["ERROR_COL"])
        
        except Exception as e:
            error_traceback = traceback.format_exc()
            logger.error(f"Error in handle_excel_saving: {error_traceback}")
            self.excel_error_label.configure(text=f"Error: {str(e)}",text_color=self.config_colors["ERROR_COL"])
            
    @log_exceptions
    def on_closing(self):
        self.destroy()
    
if __name__ == "__main__":
    try:
        logger.info("Starting application")
        app = DataValidationTool()
        app.mainloop()
        logger.info("Application closed normally")
    except Exception as e:
        logger.critical(f"Critical error in main thread: {str(e)}")
        logger.critical(traceback.format_exc())
    