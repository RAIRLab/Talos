"""
A python wrapper for integrating the DCEC* logic into the SPASS automated theorem prover.

The application provides pre-compiled binaries of SPASS for the Darwin and Linux (compiled on
Debian) systems. If the provided binaries do not work, you can download the source by going to
http://www.mpi-inf.mpg.de/departments/automation-of-logic/software/spass-workbench/ and downloading
the latest release of the 3.x branch of the code (the 4.x branch is most likely incompatible as is,
but should function with some slight modification in the spass_execute function in
talos.SpassContainer class.
"""