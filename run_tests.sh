#!/bin/bash

root_dir="./Leveled"
declare -a test_files=(
    "MC_Leveled1"
    "MC_Leveled2"
    "PC_Process1"
)

function run_test_file() {
    tlacli check \
    --cfg "${root_dir}/$1.cfg" \
    "${root_dir}/$1.tla"
}

function run_tests() {
    for index in "${!test_files[@]}"; do
        run_test_file "${test_files[index]}"
    done
}

run_tests
