#!/usr/bin/env bash

grep -EHn "^\s*(Program )?(Definition|Fixpoint|Inductive)" $1 | wc -l
