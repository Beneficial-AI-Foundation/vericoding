// <vc-preamble>
function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Simplify helpers with proper comparison functions */
function sum_lt(list1: seq<string>, list2: seq<string>): bool
{
  sum_chars_rec(list1) <= sum_chars_rec(list2)
}

function sum_eq(list1: seq<string>, list2: seq<string>): bool
{
  sum_chars_rec(list1) == sum_chars_rec(list2)
}
// </vc-helpers>

// <vc-spec>
method TotalMatch(list1: seq<string>, list2: seq<string>) returns (result: seq<string>)

  ensures |result| == |list1| || |result| == |list2|
  ensures result == list1 || result == list2
  ensures sum_chars_rec(result) <= sum_chars_rec(list1)
  ensures sum_chars_rec(result) <= sum_chars_rec(list2)
  ensures sum_chars_rec(list1) == sum_chars_rec(list2) ==> result == list1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Simple conditional assignment based on sum comparison */
  if sum_lt(list1, list2) {
    result := list1;
  } else {
    result := list2;
  }
  if sum_eq(list1, list2) {
    result := list1;
  }
}
// </vc-code>
