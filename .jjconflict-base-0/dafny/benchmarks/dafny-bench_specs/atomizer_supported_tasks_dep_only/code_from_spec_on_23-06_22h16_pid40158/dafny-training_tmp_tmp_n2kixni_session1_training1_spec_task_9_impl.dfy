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
//ATOM abs
method abs(x: int) returns (r: int)
    requires x >= 0
    ensures r >= 0
    ensures r == x
{
    r := x;
}

/** Call abs */
//ATOM foo
method foo() returns (r: int)
    ensures r >= 0
{
    r := abs(5);
}

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
//ATOM max
method max(x: int, y: int) returns (m: int)
    ensures m >= x && m >= y
    ensures m == x || m == y
{
    if x >= y {
        m := x;
    } else {
        m := y;
    }
}

/**
 *  Example 1.
 *  
 *  Try to prove 
 *  1. the final assert statement (uncomment it and you may need to strengthen pre condition).
 *  2. termination, propose a decrease clause (to replace *)
 */
//ATOM ex1
method ex1(n: int) returns (r: int)
    requires n >= 0
    ensures r == n * (n + 1) / 2
{
    r := 0;
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant r == i * (i - 1) / 2
        decreases n - i + 1
    {
        r := r + i;
        i := i + 1;
    }
}

/**
 *  Infinite loop.
 */
//ATOM foo2
method foo2() returns (r: int)
    ensures r == 0
{
    r := 0;
}

//ATOM sorted
predicate sorted(a: seq<int>) 
{
    forall j, k::0 <= j < k < |a|  ==> a[j] <= a[k]
}

//IMPL find
method find(a: seq<int>, key: int) returns (index: int)
    requires true
    ensures (index >= 0 && index < |a| && a[index] == key) || (index == -1 && key !in a)
{
    index := 0;
    while index < |a|
        invariant 0 <= index <= |a|
        invariant key !in a[..index]
    {
        if a[index] == key {
            return;
        }
        index := index + 1;
    }
    index := -1;
}

//IMPL isPalindrome
method isPalindrome(a: seq<char>) returns (b: bool) 
    ensures b <==> (forall i :: 0 <= i < |a| ==> a[i] == a[|a| - 1 - i])
{
    if |a| <= 1 {
        b := true;
        return;
    }
    
    var left := 0;
    var right := |a| - 1;
    
    while left < right
        invariant 0 <= left <= right < |a|
        /* code modified by LLM (iteration 1): added invariant to maintain palindrome property for checked pairs */
        invariant forall i :: 0 <= i < left ==> a[i] == a[|a| - 1 - i]
    {
        if a[left] != a[right] {
            b := false;
            return;
        }
        left := left + 1;
        right := right - 1;
    }
    b := true;
}

//IMPL unique
method unique(a: seq<int>) returns (b: seq<int>) 
    requires sorted(a)
    ensures sorted(b)
    ensures forall x :: x in b ==> x in a
    ensures forall x :: x in a ==> x in b
    ensures forall i, j :: 0 <= i < j < |b| ==> b[i] != b[j]
{
    if |a| == 0 {
        b := [];
        return;
    }
    
    b := [a[0]];
    var i := 1;
    
    while i < |a|
        invariant 1 <= i <= |a|
        invariant |b| >= 1
        invariant sorted(b)
        /* code modified by LLM (iteration 1): strengthened invariant for element containment */
        invariant forall x :: x in b ==> x in a
        invariant forall x :: x in a[..i] ==> x in b
        invariant forall j, k :: 0 <= j < k < |b| ==> b[j] != b[k]
        /* code modified by LLM (iteration 1): added invariant to track last element in b */
        invariant b[|b| - 1] in a[..i]
        /* code modified by LLM (iteration 1): added invariant to ensure b contains representative elements */
        invariant forall x :: x in a[..i] ==> exists j :: 0 <= j < |b| && b[j] == x
    {
        if a[i] != a[i - 1] {
            b := b + [a[i]];
        }
        i := i + 1;
    }
}

//IMPL Main
method Main() {
    var result := find([1, 2, 3, 4, 5], 3);
    print "Found at index: ", result, "\n";
    
    var palindrome := isPalindrome(['a', 'b', 'a']);
    print "Is palindrome: ", palindrome, "\n";
    
    var uniqueSeq := unique([1, 1, 2, 2, 3, 4, 4, 5]);
    print "Unique sequence: ", uniqueSeq, "\n";
}