// <vc-preamble>
function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}
// </vc-preamble>

// <vc-helpers>

function sum_helper(s: seq<int>, acc: int): int {
  if |s| == 0 then acc else sum_helper(s[1..], acc + s[0])
}
function prod_helper(s: seq<int>, acc: int): int {
  if |s| == 0 then acc else prod_helper(s[1..], acc * s[0])
}
lemma sum_helper_lemma(s: seq<int>, acc: int) 
  ensures sum_helper(s, acc) == acc + sum(s) 
{
  if |s| != 0 {
    sum_helper_lemma(s[1..], acc + s[0]);
  }
}
lemma prod_helper_lemma(s: seq<int>, acc: int) 
  ensures prod_helper(s, acc) == acc * prod(s) 
{
  if |s| != 0 {
    prod_helper_lemma(s[1..], acc * s[0]);
  }
}

// </vc-helpers>

// <vc-spec>
method sum_product(numbers: seq<int>) returns (s : int, p : int)

    ensures s == sum(numbers)
    ensures p == prod(numbers)
// </vc-spec>
// <vc-code>
{
  s := sum_helper(numbers, 0);
  p := prod_helper(numbers, 1);
  sum_helper_lemma(numbers, 0);
  prod_helper_lemma(numbers, 1);
}
// </vc-code>
