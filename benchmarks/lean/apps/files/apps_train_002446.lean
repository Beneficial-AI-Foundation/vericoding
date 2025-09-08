/-
=====Function Descriptions=====
Calendar Module
The calendar module allows you to output calendars and provides additional useful functions for them.

class calendar.TextCalendar([firstweekday])

This class can be used to generate plain text calendars.

Sample Code
>>> import calendar
>>> 
>>> print calendar.TextCalendar(firstweekday=6).formatyear(2015)
                                  2015

      January                   February                   March
Su Mo Tu We Th Fr Sa      Su Mo Tu We Th Fr Sa      Su Mo Tu We Th Fr Sa
             1  2  3       1  2  3  4  5  6  7       1  2  3  4  5  6  7
 4  5  6  7  8  9 10       8  9 10 11 12 13 14       8  9 10 11 12 13 14
11 12 13 14 15 16 17      15 16 17 18 19 20 21      15 16 17 18 19 20 21
18 19 20 21 22 23 24      22 23 24 25 26 27 28      22 23 24 25 26 27 28
25 26 27 28 29 30 31                                29 30 31

       April                      May                       June
Su Mo Tu We Th Fr Sa      Su Mo Tu We Th Fr Sa      Su Mo Tu We Th Fr Sa
          1  2  3  4                      1  2          1  2  3  4  5  6
 5  6  7  8  9 10 11       3  4  5  6  7  8  9       7  8  9 10 11 12 13
12 13 14 15 16 17 18      10 11 12 13 14 15 16      14 15 16 17 18 19 20
19 20 21 22 23 24 25      17 18 19 20 21 22 23      21 22 23 24 25 26 27
26 27 28 29 30            24 25 26 27 28 29 30      28 29 30
                          31

        July                     August                  September
Su Mo Tu We Th Fr Sa      Su Mo Tu We Th Fr Sa      Su Mo Tu We Th Fr Sa
          1  2  3  4                         1             1  2  3  4  5
 5  6  7  8  9 10 11       2  3  4  5  6  7  8       6  7  8  9 10 11 12
12 13 14 15 16 17 18       9 10 11 12 13 14 15      13 14 15 16 17 18 19
19 20 21 22 23 24 25      16 17 18 19 20 21 22      20 21 22 23 24 25 26
26 27 28 29 30 31         23 24 25 26 27 28 29      27 28 29 30
                          30 31

      October                   November                  December
Su Mo Tu We Th Fr Sa      Su Mo Tu We Th Fr Sa      Su Mo Tu We Th Fr Sa
             1  2  3       1  2  3  4  5  6  7             1  2  3  4  5
 4  5  6  7  8  9 10       8  9 10 11 12 13 14       6  7  8  9 10 11 12
11 12 13 14 15 16 17      15 16 17 18 19 20 21      13 14 15 16 17 18 19
18 19 20 21 22 23 24      22 23 24 25 26 27 28      20 21 22 23 24 25 26
25 26 27 28 29 30 31      29 30                     27 28 29 30 31

=====Problem Statement=====
You are given a date. Your task is to find what the day is on that date.

=====Input Format=====
A single line of input containing the space separated month, day and year, respectively, in MM DD YYYY format.

=====Constraints=====
2000<year<3000

=====Output Format=====
Output the correct day in capital letters.
-/

def get_weekday_name (month : Nat) (day : Nat) (year : Nat) : String := sorry

structure Date where
  month : Nat
  day : Nat 
  year : Nat

def IsValidDate (d : Date) : Prop := sorry
def weekday (d : Date) : Nat := sorry

def calendar_day_name (n : Nat) : String := sorry
def IsUppercase (s : String) : Prop := sorry

-- <vc-helpers>
-- </vc-helpers>

def IsValidWeekdayName (s : String) : Prop := sorry

theorem get_weekday_name_matches_calendar
    (m : Nat) (d : Nat) (y : Nat)
    (h1 : 1 ≤ m ∧ m ≤ 12)
    (h2 : 1 ≤ d ∧ d ≤ 31)
    (h3 : 1900 ≤ y ∧ y ≤ 2100)
    (h4 : IsValidDate ⟨m, d, y⟩) : 
    get_weekday_name m d y = calendar_day_name (weekday ⟨m, d, y⟩) := sorry

theorem get_weekday_name_returns_uppercase
    (m : Nat) (d : Nat) (y : Nat)
    (h1 : 1 ≤ m ∧ m ≤ 12) 
    (h2 : 1 ≤ d ∧ d ≤ 31)
    (h3 : 1900 ≤ y ∧ y ≤ 2100) :
    IsValidDate ⟨m, d, y⟩ →
    (IsUppercase (get_weekday_name m d y) ∧ 
     IsValidWeekdayName (get_weekday_name m d y)) := sorry

/-
info: 'WEDNESDAY'
-/
-- #guard_msgs in
-- #eval get_weekday_name 8 5 2015

/-
info: 'SUNDAY'
-/
-- #guard_msgs in
-- #eval get_weekday_name 1 1 2023

/-
info: 'MONDAY'
-/
-- #guard_msgs in
-- #eval get_weekday_name 12 25 2023

-- Apps difficulty: introductory
-- Assurance level: unguarded