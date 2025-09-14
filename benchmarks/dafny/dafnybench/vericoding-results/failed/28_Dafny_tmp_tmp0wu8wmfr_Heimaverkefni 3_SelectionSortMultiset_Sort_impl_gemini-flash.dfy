// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/dtcnY

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/ybUCz

///////////////////////////////////////////////////////////////
// Hér byrjar óbreytanlegi hluti skrárinnar.
// Fyrir aftan þann hluta er sá hluti sem þið eigið að breyta.
///////////////////////////////////////////////////////////////

// Hjálparfall sem finnur minnsta gildi í poka

method MinOfMultiset( m: multiset<int> ) returns( min: int )
    ensures min in m;
    ensures forall z | z in m :: min <= z;
{
  assume{:axiom} false;
}

// Ekki má breyta þessu falli.


///////////////////////////////////////////////////////////////
// Hér lýkur óbreytanlega hluta skrárinnar.
// Hér fyrir aftan er sá hluti sem þið eigið að breyta til að
// útfæra afbrigði af selection sort.
///////////////////////////////////////////////////////////////

// Selection sort sem raðar poka í runu.
// Klárið að forrita þetta fall.

// <vc-helpers>
method MinOfMultiset( m: multiset<int> ) returns( min: int )
    requires m != multiset{};
    ensures min in m;
    ensures forall z | z in m :: min <= z;
{
  min := m.Any();

  // Iterate through the multiset to find the minimum element.
  // The 'for var x in m' syntax is not directly supported for multisets.
  // We can use a loop with a temporary multiset to iterate.
  var temp_m := m;
  while temp_m != multiset{}
    decreases |temp_m|;
    invariant min in m;
    invariant forall z | z in m - temp_m :: min <= z; // Elements already processed are >= min
    invariant forall z | z in temp_m :: min <= z || (exists old_min | old_min in (m - temp_m) && min < old_min); // If min was updated, it's because it was smaller than some x in m - temp_m
  {
    var current_element := temp_m.Any();
    if current_element < min {
      min := current_element;
    }
    temp_m := temp_m - {current_element};
  }
}
// </vc-helpers>

// <vc-spec>
method Sort( m: multiset<int> ) returns ( s: seq<int> )
    // Setjið viðeigandi ensures klausur hér
    ensures multiset(s) == m;
    ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
// </vc-spec>
// <vc-code>
{
  var s_local: seq<int> := [];
  var current_multiset := m;

  while current_multiset != multiset{}
    invariant multiset(s_local) + current_multiset == m;
    invariant (forall p,q | 0 <= p < q < |s_local| :: s_local[p] <= s_local[q]);
    invariant forall a | a in current_multiset, b | b in multiset(s_local) :: b <= a;
    decreases |current_multiset|;
  {
    var min_val := MinOfMultiset(current_multiset);
    s_local := s_local + [min_val];
    current_multiset := current_multiset - {min_val};
  }
  return s_local;
}
// </vc-code>

