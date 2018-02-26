# SSH Fingerprint project

This small assembly x86 program reads the user input in format:
program_name.exe mode SSH_fingerprint_32b
Where mode: 
	0 - normal 
	1 - extended - in this case pointer of ASCII Art moves as if it was chess tower
Then it generates ASCII Art from SSH key fingerprint, as in OpenSSH package.

The input is required to be 16B in HEX (without marks like :, -, etc.).