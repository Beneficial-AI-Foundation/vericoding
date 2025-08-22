/*
 * Copyright 2021 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may 
 * not use this file except in compliance with the License. You may obtain 
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
 * License for the specific language governing permissions and limitations 
 * under the License.
 */

/**
 *  Example 0.a.
 *  Add pre-cond to specify x >= 0 and a post cond of your choice.
 *  Counter-example generation.
 */
//ATOM_PLACEHOLDER_abs

/** Call abs */
//ATOM_PLACEHOLDER_foo

/**
 *  Example 0.b.
 *  The goal is to compute the maximum of x and y and return it in m.
 *  The current version is buggy and returns 0 is x > y and 1 if x <= 1.
 * 
 *  Try to:
 *  1. write the post-condition that shows that max(x,y) (i.e. m) is larger than x and y.
 *  2. write a set of post-conditions that fully characterises max.
 *  3. fix the code and make sure it verifies.
 */
//ATOM_PLACEHOLDER_max

/**
 *  Example 1.
 *  
 *  Try to prove 
 *  1. the final assert statement (uncomment it and you may need to strengthen pre condition).
 *  2. termination, propose a decrease clause (to replace *)
 */
//ATOM_PLACEHOLDER_ex1

/**
 *  Infinite loop.
 */
//ATOM_PLACEHOLDER_foo2

//  Specify a post-condition and prove it.

/**
 *  Example 2.
 *
 *  Find a key in an array.
 *
 *  @param      a   The array.
 *  @param      key The key to find.
 *  @returns        An index i such a[i] == key if key in a and -1 otherwise.
 *
 *  Try to:
 *  0.  uncomment line index := index + 2 and check problems
 *  1.  write the property defined by the @returns above
 *  2.  prove this property (you may add loop invariants)
 *
 *  @note       The code below is flawed on purpose.
 *              |a| is the length of a
 *              to test whether an integer `k` is in `a`: k in a (true
 *              iff exists 0 <= i < |a|, a[i] == k). 
 *              And: !(k in a) <==> k !in a
 *              a[i..j] is the sub sequence a[i], ..., a[j - 1] 
 *              a[..j] is a[0..j] and a[i..] is a[i..|a|]
 *              a[..] is same as a
 */
//ATOM_PLACEHOLDER_find

//  Prove more complicated invariants with quantifiers.

/**
 *  Palindrome checker.
 *  Example 3.
 *
 *  Check whether a sequence of letters is a palindrome.
 *
 *  Try to:
 *  1. write the algorithm to determine whether a string is a palindrome
 *  2. write the ensures clauses that specify the palidrome properties
 *  3. verify algorithm. 
 *
 *  Notes: a[k] accesses element k of a for 0 <= k < |a|
 *  a[i..j] is (a seq) with the first j elements minus the first i
 *  a[0..|a|] is same as a.  
 */
//ATOM_PLACEHOLDER_isPalindrome

/**
 *  Whether a sequence of ints is sorted (ascending).
 *  
 *  @param  a   A sequence on integers.
 *  @returns    Whether the sequence is sorted.
 */
// ATOM 
predicate sorted(a: seq<int>) 
{
    forall j, k::0 <= j < k < |a|  ==> a[j] <= a[k]
}

/**
 *  Example 4.
 *
 *  Remove duplicates from a sorted sequence.
 *
 *  Try to:
 *  1. write the code to compute b
 *  2. write the ensures clauses that specify the remove duplicates properties
 *  3. verify algorithm. 
 *
 *  Notes: a[k] accesses element k of a for 0 <= k < |a|
 *  a[i..j] is (a seq) with the first j elements minus the first i
 *  a[0.. |a| - 1] is same as a.  
 */


/**
 *  Example 4.
 *
 *  Remove duplicates from a sorted sequence.
 *
 *  Try to:
 *  1. write the code to compute b
 *  2. write the ensures clauses that specify the remove duplicates properties
 *  3. verify algorithm. 
 *
 *  Notes: a[k] accesses element k of a for 0 <= k < |a|
 *  a[i..j] is (a seq) with the first j elements minus the first i
 *  a[0.. |a| - 1] is same as a.  
 */
//IMPL unique
method unique(a: seq<int>) returns (b: seq<int>) 
    requires sorted(a)
    ensures sorted(b)
    ensures forall i, j :: 0 <= i < j < |b| ==> b[i] != b[j]
    ensures forall x :: x in a <==> x in b
{
    b := [];
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant sorted(b)
        /* code modified by LLM (iteration 1): Added proper no duplicates invariant */
        invariant forall j, k :: 0 <= j < k < |b| ==> b[j] != b[k]
        /* code modified by LLM (iteration 1): Added invariant to ensure all elements in b come from processed part of a */
        invariant forall x :: x in b ==> x in a[..i]
        /* code modified by LLM (iteration 1): Added invariant to ensure all unique elements from processed part are in b */
        invariant forall x :: x in a[..i] ==> x in b
        /* code modified by LLM (iteration 1): Added invariant about unprocessed elements */
        invariant forall x :: x in a[i..] ==> (x in b <==> x in a[..i])
    {
        /* code modified by LLM (iteration 1): Fixed condition to properly check for duplicates */
        if |b| == 0 || a[i] != b[|b| - 1] {
            b := b + [a[i]];
        }
        i := i + 1;
    }
}

/**
 *  Dafny compiles the Main method if it finds one in a file.
 */


/**
 *  Dafny compiles the Main method if it finds one in a file.
 */
//ATOM_PLACEHOLDER_Main