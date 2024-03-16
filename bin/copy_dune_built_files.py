#!/usr/bin/env python3

import glob
import os
import shutil
import argparse

if __name__ == "__main__":
    argp = argparse.ArgumentParser()

    argp.add_argument("-d", "--dry-run", action="store_true", help="Just print out files and where they would be copied instead of actually copying them.")
    argp.add_argument("-v", "--verbose", action="store_true", help="Print out the files being copied as they're being copied.")

    args = argp.parse_args()
    build_dir = "_build/default/Imp_LangTrick"
    
    for f in (glob.glob(build_dir + "/**/*.vo", recursive=True) + glob.glob(build_dir + "/*.vo", recursive=True) + glob.glob("_build/default/Imp_LangTrick/**/*.glob", recursive=True) + glob.glob(build_dir + "/*.glob", recursive=True)):
        dest = os.path.relpath(f, "_build/default")
        if os.path.exists(os.path.dirname(dest)):
            if args.dry_run or args.verbose:
                print(f"{f}\n=>\t{dest}")
                pass
            if not args.dry_run:
                shutil.copyfile(f, dest)
                pass
            pass
        else:
            if args.verbose:
                print(f"Warning: Directory {os.path.dirname(dest)} does not exist. Skipping file {dest}")
                
