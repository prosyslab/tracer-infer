# Copyright (c) 2019-present, Facebook, Inc.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

TESTS_DIR = ../../..

# see explanations in cpp/errors/Makefile for the custom isystem
CLANG_OPTIONS = -x c++ -std=c++11 -nostdinc++ -isystem$(ROOT_DIR) -isystem$(CLANG_INCLUDES)/c++/v1/ -c
INFER_OPTIONS = --annotation-reachability-only --debug-exceptions --project-root $(TESTS_DIR) --annotation-reachability-cxx '{ "TEST_ANNOT_REACH": { "sources": { "symbols": [ "CheckFrom::" ] }, "sinks": { "symbols": [ "Danger::", "death" ] } } }'
INFERPRINT_OPTIONS = --issues-tests


SOURCES = $(wildcard *.cpp)

include $(TESTS_DIR)/clang.make

infer-out/report.json: $(MAKEFILE_LIST)