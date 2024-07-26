# IDE and Motivation
- Q: Write the run.do file. It should set up vsim, run all lines, save coverage to a default file, make the report generatr in cov.txt file, then run it.
run.do
```
vsim +access+r;
run -all;
acdb save;  // save coverage data to specific file. If no file argument is present then default
            // fcover.acdb will store coverage data
acdb report -db  fcover.acdb -txt -o cov.txt -verbose   // generate report from coverage database
                                                        // allows report to be stored in the cov.txt file,
                                                        // -verbose enable warning related to report generation
exec cat cov.txt;  // display data fom cov.txt file on console
exit
```
