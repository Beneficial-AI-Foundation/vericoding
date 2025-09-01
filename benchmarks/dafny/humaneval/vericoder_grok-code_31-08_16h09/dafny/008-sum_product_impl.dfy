function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method sum_product(numbers: seq<int>) returns (s : int, p : int)
    // post-condition-start
    ensures s == sum(numbers)
    ensures p == prod(numbers)
    // post-condition-end
// </vc-spec>
// <vc-code>
{
  if |numbers| == 0 {
    s := 0;
    p := 1;
  } else {
    var s1, p1 := sum_product(numbers[1..]);
    s := numbers[0] + s1;
    p := numbers[0] * p1;
  }
}
// </vc-code>

