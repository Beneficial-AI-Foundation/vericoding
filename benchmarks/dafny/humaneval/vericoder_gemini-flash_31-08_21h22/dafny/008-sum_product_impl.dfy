function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}

// <vc-helpers>
function sum_seq(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum_seq(s[1..])
}
function prod_seq(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod_seq(s[1..])
}
lemma sum_seq_append(s1: seq<int>, s2: seq<int>)
    ensures sum_seq(s1 + s2) == sum_seq(s1) + sum_seq(s2)
{
    if |s1| == 0 {
        assert sum_seq(s1 + s2) == sum_seq(s2);
        assert sum_seq(s1) + sum_seq(s2) == 0 + sum_seq(s2);
    } else {
        calc {
            sum_seq(s1 + s2);
            s1[0] + sum_seq(s1[1..] + s2);
            sum_seq_append(s1[1..], s2);
            s1[0] + sum_seq(s1[1..]) + sum_seq(s2);
            sum_seq(s1) + sum_seq(s2);
        }
    }
}

lemma prod_seq_append(s1: seq<int>, s2: seq<int>)
    ensures prod_seq(s1 + s2) == prod_seq(s1) * prod_seq(s2)
{
    if |s1| == 0 {
        assert prod_seq(s1 + s2) == prod_seq(s2);
        assert prod_seq(s1) * prod_seq(s2) == 1 * prod_seq(s2);
    } else {
        calc {
            prod_seq(s1 + s2);
            s1[0] * prod_seq(s1[1..] + s2);
            prod_seq_append(s1[1..], s2);
            s1[0] * prod_seq(s1[1..]) * prod_seq(s2);
            prod_seq(s1) * prod_seq(s2);
        }
    }
}
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
  s := 0;
  p := 1;
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant s == sum_seq(numbers[..i])
    invariant p == prod_seq(numbers[..i])
  {
    assert numbers[..i+1] == numbers[..i] + [numbers[i]];
    sum_seq_append(numbers[..i], [numbers[i]]);
    prod_seq_append(numbers[..i], [numbers[i]]);

    s := s + numbers[i];
    p := p * numbers[i];
    i := i + 1;
  }
}
// </vc-code>

