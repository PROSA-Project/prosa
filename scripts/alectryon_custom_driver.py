#!/usr/bin/python3

import re
import sys
from alectryon import cli
from alectryon.html import ASSETS

current_fira_version = "5.2.0"
current_ibmtype_version = "0.5.4"

assets_ibmtype_version = re.search(r"\d+\.\d+\.\d+", ASSETS.IBM_PLEX_CDN).group()
assets_fira_version = re.search(r"\d+\.\d+\.\d+", ASSETS.FIRA_CODE_CDN).group()

if str(current_ibmtype_version) == str(assets_ibmtype_version):
    # https://cdnjs.cloudflare.com/ajax/libs/IBM-type/0.5.4/css/ibm-type.min.css
    ASSETS.IBM_PLEX_CDN = (
        '<link rel="stylesheet" href="https://cdn.mpi-klsb.mpg.de/IBM-type/'
        + str(current_ibmtype_version)
        + '/css/ibm-type.min.css" />'
    )
else:
    sys.stderr.write(
        "Assets: ASSETS.IBM_PLEX_CDN changed from "
        + str(current_ibmtype_version)
        + " to "
        + str(assets_ibmtype_version)
        + "\n"
    )

if str(current_fira_version) == str(assets_fira_version):
    # https://cdnjs.cloudflare.com/ajax/libs/firacode/5.2.0/fira_code.min.css
    ASSETS.FIRA_CODE_CDN = (
        '<link rel="stylesheet" href="https://cdn.mpi-klsb.mpg.de/firacode/'
        + str(current_fira_version)
        + '/fira_code.min.css" />'
    )
else:
    sys.stderr.write(
        "Assets: FIRA_CODE_CDN changed from "
        + str(current_fira_version)
        + " to "
        + str(assets_fira_version)
        + " \n"
    )

cli.main()
