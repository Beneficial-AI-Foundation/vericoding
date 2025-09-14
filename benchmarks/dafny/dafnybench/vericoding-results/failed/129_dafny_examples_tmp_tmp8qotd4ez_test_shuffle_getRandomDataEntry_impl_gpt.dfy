method random(a: int, b: int) returns (r: int)
//  requires a <= b
  ensures a <= b ==> a <= r <= b

function set_of_seq<T>(s: seq<T>): set<T>
{
  set x: T | x in s :: x
}

// <vc-helpers>
lemma ProperSubsetHasWitness<T>(A: set<T>, B: set<T>)
  requires A < B
  ensures exists x: T :: x in B && x !in A
{
  if (forall x: T :: x in B ==> x in A) {
    assert B <= A;
    assert A <= B;
    assert A == B;
    assert false;
  }
}

lemma SeqSetMembershipEquiv<T>(x: T, s: seq<T>)
  ensures (x in set_of_seq(s)) == (x in s)
{
  assert (x in set y: T | y in s :: y) == (x in s);
}
// </vc-helpers>

// <vc-spec>
method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: seq<T>) returns (e: T)
  requires m_workList.Length > 0
  ensures set_of_seq(avoidSet) < set_of_seq(m_workList[..]) ==> e !in avoidSet
  ensures avoidSet < m_workList[..] ==> e in m_workList[..]
// </vc-spec>
// <vc-code>
{
  if set_of_seq(avoidSet) < set_of_seq(m_workList[..]) {
    ghost call ProperSubsetHasWitness(set_of_seq(avoidSet), set_of_seq(m_workList[..]));
    var x: T :| x in set_of_seq(m_workList[..]) && x !in set_of_seq(avoidSet);
    e := x;
    assert (e in set_of_seq(avoidSet)) == (e in avoidSet);
    assert (e in set_of_seq(m_workList[..])) == (e in m_workList[..]);
  } else {
    e := m_workList[0];
  }
}
// </vc-code>

