=====Problem Statement=====
You are asked to ensure that the first and last names of people begin with a capital letter in their passports. For example, alison heck should be capitalised correctly as Alison Heck. 

alison heck => Alison Heck

Given a full name, your task is to capitalize the name appropriately.

=====Input Format=====
A single line of input containing the full name, S.

=====Constraints=====
0<len(S)<1000
The string consists of alphanumeric characters and spaces.

Note: in a word only the first character is capitalized. Example 12abc when capitalized remains 12abc.

=====Output Format=====
Print the capitalized string, S.

def toString (s : List Char) : String := sorry
def capitalize_name (s : String) : String := sorry

def splitOn (s : String) (p : Char → Bool) : List String := sorry
def front (s : String) : Char := sorry

def drop (s : String) (n : Nat) : String := sorry
def isAlpha (c : Char) : Bool := sorry

def isUpper (c : Char) : Bool := sorry
def toLower (s : String) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded