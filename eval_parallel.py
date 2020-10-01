import os, sys, subprocess
from multiprocessing import Pool
from subprocess import call

def f(x):
    # print(x)
    call(["./smartscopy", x])
    # call(["racket", "smartscopy.rkt", x])

def main():
    # print command line arguments
    dir_loc = sys.argv[1]
    file_list = os.listdir(dir_loc)
    full_list = list(map(lambda x: (dir_loc + x), file_list))
    with Pool(8) as p:
        p.map(f, full_list)

if __name__ == "__main__":
    main()
