import Std
import Mathlib

open Std.Do

/-!
{
  "name": "Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_aula3_sumBackwards",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_aula3_sumBackwards",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/-- Fibonacci function translated from Dafny -/
partial def fib (n : Nat) : Nat :=
  if n == 0 then 1
  else if n == 1 then 1
  else fib (n-1) + fib (n-2)

/-- List datatype translated from Dafny -/
inductive List (T : Type)
  | Nil : List T
  | Cons : T → List T → List T

/-- Add function for lists translated from Dafny -/
def add : List Int → Int
  | List.Nil => 0
  | List.Cons x xs => x + add xs

/-- Sum function translated from Dafny -/
partial def sum (n : Nat) : Nat :=
  if n == 0 then 0
  else n + sum (n-1)

/-- sumBackwards method translated from Dafny -/
def sumBackwards (n : Nat) : Nat := sorry

/-- Specification for sumBackwards -/
theorem sumBackwards_spec (n : Nat) :
  sumBackwards n = sum n := sorry

end DafnyBenchmarks
