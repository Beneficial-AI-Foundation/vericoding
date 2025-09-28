// <vc-preamble>

predicate ValidInput(lst: seq<int>)
{
    forall i :: 0 <= i < |lst| ==> lst[i] >= 0
}

predicate IsSortedAscending(lst: seq<int>)
{
    forall i, j :: 0 <= i < j < |lst| ==> lst[i] <= lst[j]
}

predicate NoMoreThanTwoDuplicates(lst: seq<int>)
{
    forall i :: 0 <= i < |lst| ==> count_occurrences(lst, lst[i]) <= 2
}

predicate ValidList(lst: seq<int>)
{
    ValidInput(lst) && IsSortedAscending(lst) && NoMoreThanTwoDuplicates(lst)
}
function count_occurrences(lst: seq<int>, value: int): int
    ensures count_occurrences(lst, value) >= 0
    ensures count_occurrences(lst, value) <= |lst|
    ensures count_occurrences(lst, value) == 0 <==> value !in lst
{
    if |lst| == 0 then 0
    else if lst[0] == value then 1 + count_occurrences(lst[1..], value)
    else count_occurrences(lst[1..], value)
}

function has_more_than_two_occurrences(lst: seq<int>, index: int): bool
    requires 0 <= index <= |lst|
    ensures has_more_than_two_occurrences(lst, index) == (exists i :: index <= i < |lst| && count_occurrences(lst, lst[i]) > 2)
    decreases |lst| - index
{
    if index == |lst| then false
    else if count_occurrences(lst, lst[index]) > 2 then true
    else has_more_than_two_occurrences(lst, index + 1)
}

function is_sorted_ascending(lst: seq<int>, index: int): bool
    requires 0 <= index <= |lst|
    ensures is_sorted_ascending(lst, index) == (forall i, j :: index <= i < j < |lst| ==> lst[i] <= lst[j])
    decreases |lst| - index
{
    if index >= |lst| - 1 then true
    else if lst[index] > lst[index + 1] then false
    else is_sorted_ascending(lst, index + 1)
}

function is_sorted(lst: seq<int>): bool
    requires ValidInput(lst)
    ensures |lst| <= 1 ==> is_sorted(lst) == true
    ensures is_sorted(lst) == (IsSortedAscending(lst) && NoMoreThanTwoDuplicates(lst))
{
    if |lst| <= 1 then true
    else if !is_sorted_ascending(lst, 0) then false
    else !has_more_than_two_occurrences(lst, 0)
}
// </vc-preamble>

// <vc-helpers>
function count_occurrences_helper(lst: seq<int>, value: int, start: int): int
  requires 0 <= start <= |lst|
  ensures count_occurrences_helper(lst, value, start) == count_occurrences(lst[start..], value)
  decreases |lst| - start
{
  if start == |lst| then 0
  else if lst[start] == value then 1 + count_occurrences_helper(lst, value, start + 1)
  else count_occurrences_helper(lst, value, start + 1)
}

function check_sorted_ascending(lst: seq<int>, index: int): bool
  requires 0 <= index <= |lst|
  ensures check_sorted_ascending(lst, index) == (forall i, j :: index <= i < j < |lst| ==> lst[i] <= lst[j])
  decreases |lst| - index
{
  if index >= |lst| - 1 then true
  else if lst[index] > lst[index + 1] then false
  else check_sorted_ascending(lst, index + 1)
}

function check_duplicates(lst: seq<int>, index: int): bool
  requires 0 <= index <= |lst|
  ensures check_duplicates(lst, index) == (forall i :: index <= i < |lst| ==> count_occurrences(lst, lst[i]) <= 2)
  decreases |lst| - index
{
  if index == |lst| then true
  else if count_occurrences_helper(lst, lst[index], 0) > 2 then false
  else check_duplicates(lst, index + 1)
}
// </vc-helpers>

// <vc-spec>
method CheckValidList(lst: seq<int>) returns (result: bool)
    requires ValidInput(lst)
    ensures result == ValidList(lst)
    ensures result == (IsSortedAscending(lst) && NoMoreThanTwoDuplicates(lst))
// </vc-spec>
// <vc-code>
{
  if |lst| <= 1 {
    result := true;
  } else {
    var sorted := check_sorted_ascending(lst, 0);
    var duplicates := check_duplicates(lst, 0);
    result := sorted && duplicates;
  }
}
// </vc-code>
