#!/bin/bash

root_dir="./specs"
declare -a test_files=(
    "leveled_sync"
    "leveled_eventual"
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
