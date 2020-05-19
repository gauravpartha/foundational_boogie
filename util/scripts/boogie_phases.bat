@echo off

set CUR_YYYY=%date:~10,4%
set CUR_MM=%date:~4,2%
set CUR_DD=%date:~7,2%
set CUR_HH=%time:~0,2%
if %CUR_HH% lss 10 (set CUR_HH=0%time:~1,1%)
set CUR_NN=%time:~3,2%
set CUR_SS=%time:~6,2%

set TIME_PREFIX=%CUR_YYYY%%CUR_MM%%CUR_DD%-%CUR_HH%%CUR_NN%%CUR_SS%
set SMT_OUTPUT=%TIME_PREFIX%_boogie.smt2
set LOG_OUTPUT=%TIME_PREFIX%_boogie_log.txt

set CUR_NN=%time:~3,2%

set BOOGIE=boogie
set BOOGIE_OPTS=/traceTimes /tracePOs /traceverify /trace /proverLog:%SMT_OUTPUT%
set BOOGIE_OPTS_MORE= %*
set CMD=%BOOGIE% %BOOGIE_OPTS% %BOOGIE_OPTS_MORE%

call %CMD% > %LOG_OUTPUT%