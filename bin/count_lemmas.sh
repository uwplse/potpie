#!/usr/bin/env bash

grep -EHn "^\s*(Lemma|Theorem|Corollary)" $1 | wc -l 
