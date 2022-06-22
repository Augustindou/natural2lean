import platform
import os
import shutil
from ..translator import DEFAULT_PATHS, GIT_LOCATION, LEAN_PROJECT_GIT_REPO


def update_git():
    try:
        path = DEFAULT_PATHS[platform.system()]
    except KeyError:
        raise Exception(
            f"Unsupported platform: `{platform.system()}`, please report this bug."
        )

    if path.exists():
        # run git pull
        print("Updating lean project template...\n")
        os.system(
            f'git --work-tree="{path}" --git-dir="{path/GIT_LOCATION}" reset --hard'
        )
        os.system(f'git --work-tree="{path}" --git-dir="{path/GIT_LOCATION}" pull')
        print()

    else:
        # run git clone
        path.mkdir(parents=True)
        print("Downloading lean project template...\n")
        os.system(f"git clone {LEAN_PROJECT_GIT_REPO} {path}")
        print()


def reset_git():
    try:
        path = DEFAULT_PATHS[platform.system()]
    except KeyError:
        raise Exception(
            f"Unsupported platform: `{platform.system()}`, please report this bug."
        )

    # remove the folder if it exists
    if path.exists():
        shutil.rmtree(path)

    # run git clone
    path.mkdir(parents=True)
    print("Downloading lean project template...\n")
    os.system(f"git clone {LEAN_PROJECT_GIT_REPO} {path}")
    print()
