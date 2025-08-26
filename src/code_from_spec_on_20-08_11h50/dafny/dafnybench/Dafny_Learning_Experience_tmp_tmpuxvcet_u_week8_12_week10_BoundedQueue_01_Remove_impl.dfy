class BoundedQueue<T(0)>
{
 // abstract state
 ghost var contents: seq<T> // the contents of the bounded queue
 ghost var N: nat // the (maximum) size of the bounded queue
 ghost var Repr: set<object>
 // concrete state
var data: array<T>
 var wr: nat
 var rd: nat

  ghost predicate Valid()
 reads this, Repr
ensures Valid() ==> this in Repr && |contents| <= N 
 {
 this in Repr && data in Repr &&
data.Length == N + 1 &&
wr <= N && rd <= N &&
 contents == if rd <= wr then data[rd..wr] else data[rd..] + data[..wr]
 }

// <vc-spec>
 constructor (N: nat)
ensures Valid() && fresh(Repr)
ensures contents == [] && this.N == N
{
 contents := [];
 this.N := N;
 data := new T[N+1]; // requires T to have default initial value
 rd, wr := 0, 0;
 Repr := {this, data};
}

// <vc-helpers>
lemma RemoveContentsLemma(old_rd: nat, old_wr: nat, old_contents: seq<T>)
  requires this.data != null
  requires old_rd <= N && old_wr <= N
  requires data.Length == N + 1
  requires old_contents == if old_rd <= old_wr then data[old_rd..old_wr] else data[old_rd..] + data[..old_wr]
  requires |old_contents| > 0
  ensures var new_rd := (old_rd + 1) % data.Length;
          var new_contents := if new_rd <= old_wr then data[new_rd..old_wr] else data[new_rd..] + data[..old_wr];
          new_contents == old_contents[1..]
{
  var new_rd := (old_rd + 1) % data.Length;
  var new_contents := if new_rd <= old_wr then data[new_rd..old_wr] else data[new_rd..] + data[..old_wr];
  
  if old_rd <= old_wr {
    // Case 1: no wraparound in old contents
    if old_rd + 1 <= old_wr {
      // new_rd is still <= old_wr
      assert new_rd == old_rd + 1;
      assert new_contents == data[old_rd + 1..old_wr];
      assert old_contents == data[old_rd..old_wr];
      assert new_contents == old_contents[1..];
    } else {
      // old_rd + 1 == old_wr, so queue becomes empty
      assert old_rd + 1 == old_wr;
      assert |old_contents| == 1;
      assert new_contents == [];
      assert old_contents[1..] == [];
    }
  } else {
    // Case 2: wraparound in old contents
    if old_rd < N {
      // new_rd = old_rd + 1, still > old_wr
      assert new_rd == old_rd + 1;
      assert new_rd > old_wr;
      assert new_contents == data[old_rd + 1..] + data[..old_wr];
      assert old_contents == data[old_rd..] + data[..old_wr];
      assert data[old_rd..] == [data[old_rd]] + data[old_rd + 1..];
      assert new_contents == old_contents[1..];
    } else {
      // old_rd == N, so new_rd wraps to 0
      assert old_rd == N;
      assert new_rd == 0;
      if old_wr == 0 {
        // Queue becomes empty
        assert |old_contents| == 1;
        assert new_contents == [];
        assert old_contents[1..] == [];
      } else {
        // new_rd <= old_wr
        assert new_contents == data[0..old_wr];
        assert old_contents == data[N..] + data[..old_wr];
        assert data[N..] == [data[N]];
        assert data[..old_wr] == data[0..old_wr];
        assert new_contents == old_contents[1..];
      }
    }
  }
}
// </vc-helpers>

method Remove() returns (x:T)
requires Valid()
requires |contents| != 0
modifies Repr
ensures contents == old(contents[1..]) && old(contents[0]) == x
ensures N == old(N)
ensures Valid() && fresh(Repr - old(Repr))
// </vc-spec>
// <vc-code>
{
  var old_rd := rd;
  var old_wr := wr;
  var old_contents := contents;
  
  x := data[rd];
  rd := (rd + 1) % data.Length;
  
  // Update contents based on new rd and wr values
  contents := if rd <= wr then data[rd..wr] else data[rd..] + data[..wr];
  
  // Prove that x is the first element of old contents
  if old_rd <= old_wr {
    assert old_contents == data[old_rd..old_wr];
    assert x == data[old_rd];
    assert old_contents[0] == data[old_rd];
  } else {
    assert old_contents == data[old_rd..] + data[..old_wr];
    assert x == data[old_rd];
    assert old_contents[0] == data[old_rd];
  }
  
  // Use lemma to prove contents relationship
  RemoveContentsLemma(old_rd, old_wr, old_contents);
  
  assert contents == old_contents[1..];
}
// </vc-code>

}