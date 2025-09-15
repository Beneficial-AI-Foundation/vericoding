// <vc-preamble>
function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}
// </vc-preamble>

// <vc-helpers>
function sum_chars_tail(list: seq<string>, acc: nat): nat
{
  if |list| == 0 then acc
  else sum_chars_tail(list[1..], acc + |list[0]|)
}

lemma sum_chars_tail_eq(list: seq<string>, acc: nat)
  ensures sum_chars_tail(list, acc) == acc + sum_chars_rec(list)
{
  if |list| == 0 {
  } else {
    calc {
      sum_chars_tail(list, acc);
      sum_chars_tail(list[1..], acc + |list[0]|);
      == { sum_chars_tail_eq(list[1..], acc + |list[0]|); }
      (acc + |list[0]|) + sum_chars_rec(list[1..]);
      acc + (|list[0]| + sum_chars_rec(list[1..]));
      == { reveal sum_chars_rec(); }
      acc + sum_chars_rec(list);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method SumChars(list: seq<string>) returns (sum: nat)

  ensures sum == sum_chars_rec(list)
// </vc-spec>
// <vc-code>
{
  sum_chars_tail_eq(list, 0);
  sum := sum_chars_tail(list, 0);
}
// </vc-code>
