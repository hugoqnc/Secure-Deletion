#!/bin/bash

# this script is invoked as part of CI to verify all packages

scriptDir=$(dirname "$0")

# flag whether this script is currently executed as part of a CI
isCi=$CI

# create .gobra folder if it does not exist yet:
mkdir -p $scriptDir/.gobra

preArgs="/usr/local/Cellar/openjdk/19.0.2/bin/java"
gobraJar="/Users/hugoqueinnec/Documents/ETH/Thesis/gobra/target/scala-2.13/gobra.jar"

# check if the argument -o is given, then use ".modulesOriginal", else use ".modules"
if [[ $* == *-o* ]]; then
    modulesDir=".modulesOriginal"
else
    modulesDir=".modules"
fi

additionalGobraArgs="-I $scriptDir/verification -I $scriptDir/.modules-precedence -I /Users/hugoqueinnec/Documents/ETH/Thesis/modules/$modulesDir -I $scriptDir --module github.com/ModularVerification/casestudies/wireguard --gobraDirectory $scriptDir/.gobra --parallelizeBranches"

packages=""
for arg in "$@"; do
    if [[ $arg != -* ]]; then
        packages+="$arg "
    fi
done

if [ -n "$packages" ]; then
    if [ "$packages" = "all " ]; then
        echo "Verifying all packages"
        packages="common messageCommon messageInitiator messageResponder labelLemma labelLemmaCommon labelLemmaInitiator labelLemmaResponder initiator responder" # These are the only packages that are supposed to verify (`main` does not verify)
    else
        echo "Verifying package(s): $packages"
    fi
fi

additionalGobraArgs="$additionalGobraArgs --includePackages $packages"

if [ $isCi ]; then
    echo -e "\033[0Ksection_start:`date +%s`:verify[collapsed=true]\r\033[0KVerifying packages"
fi
$preArgs -Xss128m -jar $gobraJar --recursive $additionalGobraArgs
exitCode=$?
if [ $isCi ]; then
    echo -e "\033[0Ksection_end:`date +%s`:verify\r\033[0K"
fi

# set exit code:
exit $exitCode
