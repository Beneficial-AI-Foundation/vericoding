

// <vc-helpers>
lemma lemma_floor_div_properties(p: int, q: int)
  ensures (p + q) / 2 * 2 <= p + q
  ensures (p + q) / 2 * 2 >= p + q - 1
{
  var k := (p + q) / 2;
  calc {
    k * 2;
    (p + q) / 2 * 2;
    <= p + q; // By definition of integer division
  }
  calc {
    k * 2;
    >= (p + q) - 2 + 1; // Since k*2 is an integer, k*2 can be (p+q)-1 or (p+q)
    >= (p + q) - 1;
  }
}

lemma lemma_mid_properties(p: int, q: int, m: int)
  requires p <= q
  requires p <= m <= q
  requires m - p <= q - m
  requires 0 <= (q - m) - (m - p) <= 1
  ensures true
{}
// </vc-helpers>

// <vc-spec>
method Mid( p: int, q: int) returns ( m: int )
    // | ... | ??? | ... |
    //        p m   q
    requires p <= q;
    ensures p<= m <= q;
    ensures m-p <= q-m;
    ensures 0 <= (q-m)-(m-p) <= 1;
// </vc-spec>
// <vc-code>
{
  var sum_pq := p + q;
  var sum_pq_div_2 := sum_pq / 2;
  m := sum_pq_div_2;

  // Prove p <= m <= q
  // p <= m:
  // p <= (p+q)/2 <=> 2p <= p+q <=> p <= q (True by precondition)
  calc {
    p;
    <= (p+q)/2; // Because p <= q implies 2p <= p + q
    m;
  }
  // m <= q:
  // (p+q)/2 <= q <=> p+q <= 2q <=> p <= q (True by precondition)
  calc {
    m;
    (p+q)/2;
    <= q; // Because p <= q implies p+q <= 2q
  }

  // Prove m-p <= q-m
  // m-p <= q-m <=> 2m <= p+q
  // We need to show 2 * ((p+q)/2) <= p+q.
  lemma_floor_div_properties(p, q);
  assert 2 * m <= p + q; // This holds by the first ensures clause of lemma_floor_div_properties

  // Prove 0 <= (q-m)-(m-p) <= 1
  // (q-m)-(m-p) = q - 2m + p
  // Lower bound: q - 2m + p >= 0
  // Since 2m <= p+q, then -(2m) >= -(p+q).
  // So q - 2m + p >= q - (p+q) + p = q - p - q + p = 0.
  calc {
    q - 2 * m + p;
    >= q - (p+q) + p;
    == q - p - q + p;
    == 0;
  }

  // Upper bound: q - 2m + p <= 1
  // We need to show p+q - 2 * ((p+q)/2) <= 1.
  // We know from lemma_floor_div_properties that 2 * ((p+q)/2) >= p+q - 1.
  // So -(2 * ((p+q)/2)) <= -(p+q - 1) = 1 - (p+q).
  // Therefore, p+q - 2 * ((p+q)/2) <= p+q + (1 - (p+q)) = 1.
  calc {
    q - 2 * m + p;
    == (p+q) - 2 * m;
    <= (p+q) - ( (p+q) - 1 ); // By lemma_floor_div_properties(p,q)
    == (p+q) - p - q + 1;
    == 1;
  }
}
// </vc-code>

