@echo off
tasm /l /zi ak_ctp.asm
tlink /v ak_ctp.obj io.obj

echo
echo testing normal operation
echo should be 127.64.22.27,"HELLO"
ak_ctp.exe < TEST_A.txt

echo
echo testing normal operation
echo should be 192.168.1.10,"23-OCT-08"
ak_ctp.exe < TEST_B.txt

echo
echo testing high IP address and empty message
echo should be 255.255.255.255,""
ak_ctp.exe < TEST_C.txt

echo
echo testing low IP address and empty message
echo should be 0.0.0.0,""
ak_ctp.exe < TEST_D.txt

echo
echo testing normal IP address and empty message
echo should be 100.101.102.103,""
ak_ctp.exe < TEST_E.txt
