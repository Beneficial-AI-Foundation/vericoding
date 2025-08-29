import Mathlib

/-!
# Common definitions for Clever benchmark specifications

These are helper predicates and functions used across multiple problem specs.
-/

/-- Check if parentheses are balanced -/
def balanced_paren_non_computable (s : String) (open' : Char) (close : Char) : Prop :=
  let chars := s.data
  let rec helper (cs : List Char) (depth : Int) : Prop :=
    match cs with
    | [] => depth = 0
    | c :: rest =>
      if c = open' then helper rest (depth + 1)
      else if c = close then depth > 0 ∧ helper rest (depth - 1)
      else helper rest depth
  helper chars 0

/-- Count maximum depth of nested parentheses -/
def count_max_paren_depth (s : String) : Nat :=
  let chars := s.data
  let rec helper (cs : List Char) (depth : Nat) (max_depth : Nat) : Nat :=
    match cs with
    | [] => max_depth
    | c :: rest =>
      if c = '(' then helper rest (depth + 1) (max depth + 1 max_depth)
      else if c = ')' then helper rest (if depth > 0 then depth - 1 else 0) max_depth
      else helper rest depth max_depth
  helper chars 0 0

/-- Count number of parenthesis groups -/
def count_paren_groups (s : String) : Nat :=
  let chars := s.data
  let rec helper (cs : List Char) (depth : Nat) (groups : Nat) : Nat :=
    match cs with
    | [] => groups
    | c :: rest =>
      if c = '(' then helper rest (depth + 1) groups
      else if c = ')' then 
        if depth = 1 then helper rest 0 (groups + 1)
        else helper rest (if depth > 0 then depth - 1 else 0) groups
      else helper rest depth groups
  helper chars 0 0

/-- Check if a string is a palindrome -/
def is_palindrome (s : String) : Bool :=
  let chars := s.data
  chars = chars.reverse

-- LLM HELPER
def collatz_step (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

-- LLM HELPER
def collatz_sequence (n : Nat) (steps : Nat) : Nat :=
  match steps with
  | 0 => n
  | k + 1 => collatz_sequence (collatz_step n) k

/-- Check if n is reachable in the Collatz sequence starting from m -/
def collatz_reachable (m n : Nat) : Prop :=
  ∃ k : Nat, collatz_sequence m k = n

/-- Check if s2 is a subsequence of s1 -/
def is_subsequence (s1 s2 : String) : Bool :=
  let chars1 := s1.data
  let chars2 := s2.data
  let rec helper (cs1 cs2 : List Char) : Bool :=
    match cs2 with
    | [] => true
    | c2 :: rest2 =>
      match cs1 with
      | [] => false
      | c1 :: rest1 =>
        if c1 = c2 then helper rest1 rest2
        else helper rest1 cs2
  helper chars1 chars2

/-- Check if brackets are balanced -/
def balanced_bracket_non_computable (s : String) : Prop :=
  let chars := s.data
  let rec helper (cs : List Char) (depth : Int) : Prop :=
    match cs with
    | [] => depth = 0
    | c :: rest =>
      if c = '[' then helper rest (depth + 1)
      else if c = ']' then depth > 0 ∧ helper rest (depth - 1)
      else helper rest depth
  helper chars 0

/-- Count occurrences of substring in string -/
def count_string_occurrence (s sub : String) : Nat :=
  if sub.length = 0 then 0
  else
    let rec helper (pos : Nat) (count : Nat) : Nat :=
      if pos + sub.length > s.length then count
      else if s.extract pos (pos + sub.length) = sub then
        helper (pos + 1) (count + 1)
      else helper (pos + 1) count
    helper 0 0

-- LLM HELPER
def is_prime_aux (n k : Nat) : Bool :=
  if k * k > n then true
  else if n % k = 0 then false
  else is_prime_aux n (k + 1)

/-- Primality test -/
def is_prime (n : Nat) : Bool :=
  if n < 2 then false
  else is_prime_aux n 2

/-- Check if all elements in list are same -/
def all_same {α : Type} [DecidableEq α] (l : List α) : Bool :=
  match l with
  | [] => true
  | x :: xs => xs.all (· = x)

-- LLM HELPER
def parse_int_aux (chars : List Char) (acc : Int) (sign : Int) : Option Int :=
  match chars with
  | [] => some (sign * acc)
  | c :: rest =>
    if c.isDigit then
      parse_int_aux rest (acc * 10 + (c.toNat - '0'.toNat)) sign
    else none

/-- Convert string to integer -/
def string_to_int (s : String) : Option Int :=
  let chars := s.data
  match chars with
  | [] => none
  | '-' :: rest => parse_int_aux rest 0 (-1)
  | '+' :: rest => parse_int_aux rest 0 1
  | _ => parse_int_aux chars 0 1

-- LLM HELPER
def sum_of_squares_of_digits (n : Nat) : Nat :=
  let rec helper (m : Nat) (acc : Nat) : Nat :=
    if m = 0 then acc
    else
      let digit := m % 10
      helper (m / 10) (acc + digit * digit)
  if n = 0 then 0 else helper n 0

-- LLM HELPER
def is_happy_aux (n : Nat) (seen : List Nat) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    if n = 1 then true
    else if n ∈ seen then false
    else is_happy_aux (sum_of_squares_of_digits n) (n :: seen) fuel'

/-- Check if a number is happy -/
def is_happy (n : Nat) : Bool :=
  is_happy_aux n [] 1000

/-- Factorial function -/
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | k + 1 => (k + 1) * factorial k

/-- GCD function -/
def gcd (a b : Nat) : Nat :=
  Nat.gcd a b

/-- LCM function -/
def lcm (a b : Nat) : Nat :=
  if a = 0 ∨ b = 0 then 0 else (a * b) / (gcd a b)

-- LLM HELPER
def is_perfect_square_aux (n k : Nat) : Bool :=
  if k * k = n then true
  else if k * k > n then false
  else is_perfect_square_aux n (k + 1)

/-- Check if number is perfect square -/
def is_perfect_square (n : Nat) : Bool :=
  is_perfect_square_aux n 0

/-- Fibonacci function -/
def fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | k + 2 => fib (k + 1) + fib k

/-- Check if list is sorted -/
def is_sorted {α : Type} [LE α] (l : List α) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: y :: rest => x ≤ y && is_sorted (y :: rest)

-- LLM HELPER
def binary_search_aux {α : Type} [LE α] [DecidableEq α] [LinearOrder α] 
    (l : List α) (x : α) (left right : Nat) : Option Nat :=
  if left > right then none
  else
    let mid := (left + right) / 2
    match l.get? mid with
    | none => none
    | some val =>
      if val = x then some mid
      else if val < x then binary_search_aux l x (mid + 1) right
      else binary_search_aux l x left (if mid = 0 then 0 else mid - 1)

/-- Binary search -/
def binary_search {α : Type} [LE α] [DecidableEq α] (l : List α) (x : α) : Option Nat :=
  if l.isEmpty then none
  else
    -- For general LE, we'll use a simpler linear search approach
    l.findIdx? (· = x)