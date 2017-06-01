#!/usr/bin/env python

import sys
import os.path

mathpartir_url = "http://cristal.inria.fr/~remy/latex/mathpartir.sty"
mathpartir_file = "mathpartir.sty"

if os.path.isfile(mathpartir_file):
    print ("{0} already exists, exiting.".format(mathpartir_file))
else:
    if sys.version_info[0] < 3:
        from urllib import urlretrieve
    else:
        from urllib.request import urlretrieve
    urlretrieve (mathpartir_url, "mathpartir.sty")
    print ("{0} downloaded.".format(mathpartir_file))
