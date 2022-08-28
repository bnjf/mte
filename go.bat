
@rem \tasm\bin\tasm /s /v /m \mte\mte.asm

@rem copy \mte\mte.asm mte.asm

@rem tasm /w+ /v /m rnd
@rem tasm /w+ /v /m mte
@rem tlink /x /t demovir rnd mte

make.bat

\shutdown

