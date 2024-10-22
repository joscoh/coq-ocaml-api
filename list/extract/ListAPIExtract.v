From Coq Require Import Extraction.
From CoqCompat Require Import ExtractUtil.
From ListAPI Require Import ListAPI.

Extract Inlined Constant Failure => "Failure".
Extract Inlined Constant InvalidArg => "Invalid_argument".

Separate Extraction ListAPI.