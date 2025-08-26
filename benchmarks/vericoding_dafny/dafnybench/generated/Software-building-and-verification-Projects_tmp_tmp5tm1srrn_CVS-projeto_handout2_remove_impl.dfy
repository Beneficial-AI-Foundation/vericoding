lemma list_remove_preserves_other_elements<K(==,!new),V(!new)>(k: K, k': K, v: V, l: List<(K,V)>)
  ensures k != k' ==> (mem((k',v), l) <==> mem((k',v), list_remove(k, l)))
{
  // Dafny can prove this automatically from the postcondition of list_remove
}

lemma list_remove_removes_key<K(==,!new),V(!new)>(k: K, v: V, l: List<(K,V)>)
  ensures !mem((k,v), list_remove(k, l))
{
  // Dafny can prove this automatically from the postcondition of list_remove
}

datatype List<T> = Nil | Cons(head:T,tail:List<T>)
datatype Option<T> = None | Some(elem:T)

ghost function mem<T>(x:T,l:List<T>) : bool {
  match l {
    case Nil => false
    case Cons(y,xs) => x==y || mem(x,xs)
  }
}

ghost function length<T>(l:List<T>) : int {
  match l {
    case Nil => 0
    case Cons(_,xs) => 1 + length(xs)
  }
}

// <vc-spec>
function list_find<K(==),V(!new)>(k:K,l:List<(K,V)>) : Option<V>
  ensures match list_find(k,l) {
            case None => forall v :: !mem((k,v),l)
            case Some(v) => mem((k,v),l)
          }
  decreases l
{
  match l {
    case Nil => None
    case Cons((k',v),xs) => if k==k' then Some(v) else list_find(k,xs)
  }
}

function list_remove<K(==,!new),V(!new)>(k:K, l:List<(K,V)>) : List<(K,V)>
  decreases l
  ensures forall k',v :: mem((k',v),list_remove(k,l)) <==> (mem((k',v),l) && k != k')
{
  match l {
    case Nil => Nil
    case Cons((k',v),xs) => if k==k' then list_remove(k,xs) else
    Cons((k',v),list_remove(k,xs))
  }
}


class Hashtable<K(==,!new),V(!new)> {
  var size : int
  var data : array<List<(K,V)>>

  ghost var Repr : set<object>
  ghost var elems : map<K,Option<V>>

  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && data in Repr && data.Length > 0 &&
    (forall i :: 0 <= i < data.Length ==> valid_hash(data, i)) &&
    (forall k,v :: valid_data(k,v,elems,data))
  }

  ghost predicate valid_hash(data: array<List<(K,V)>>, i: int)
    requires 0 <= i < data.Length
    reads data
  {
    forall k,v :: mem((k,v), data[i]) ==> (bucket(k,data.Length) == i)
  }


  ghost predicate valid_data(k: K,v: V,elems: map<K, Option<V>>, data: array<List<(K,V)>>)
    reads this, Repr, data
    requires data.Length > 0
  {
    (k in elems && elems[k] == Some(v)) <==> mem((k,v), data[bucket(k, data.Length)])
  }


  function hash(key:K) : int
    ensures hash(key) >= 0
  {
    42  // placeholder implementation that satisfies the postcondition
  }

  function bucket(k: K, n: int) : int
    requires n > 0
    ensures 0 <= bucket(k, n) < n
  {
    hash(k) % n
  }

  constructor(n:int)
    requires n > 0
    ensures RepInv()
    ensures fresh(Repr-{this})
    ensures elems == map[]
    ensures size == 0
  {
    size := 0;
    data := new List<(K,V)>[n](i => Nil);
    Repr := {this, data};
    elems := map[];
  }

// <vc-helpers>
lemma list_remove_preserves_other_elements_helper<K(==,!new),V(!new)>(k: K, k': K, v: V, l: List<(K,V)>)
  ensures k != k' ==> (mem((k',v), l) <==> mem((k',v), list_remove(k, l)))
{
  // Dafny can prove this automatically from the postcondition of list_remove
}

lemma list_remove_removes_key_helper<K(==,!new),V(!new)>(k: K, v: V, l: List<(K,V)>)
  ensures !mem((k,v), list_remove(k, l))
{
  // Dafny can prove this automatically from the postcondition of list_remove
}

lemma valid_data_connection<K(==,!new),V(!new)>(k: K, elems: map<K,Option<V>>, data: array<List<(K,V)>>, b: int)
  requires data.Length > 0
  requires b == bucket(k, data.Length)
  requires 0 <= b < data.Length
  ensures (k in elems && match elems[k] { case None => false case Some(_) => true }) <==> (exists v :: mem((k,v), data[b]))
{
  if k in elems && elems[k].Some? {
    var v := elems[k].elem;
    assert mem((k,v), data[b]);
  }
}
// </vc-helpers>

method remove(k: K)
    requires RepInv()
    ensures RepInv()
    ensures fresh(Repr - old(Repr))
    ensures k !in elems || elems[k] == None
    ensures forall key :: key != k && key in old(elems) ==> key in elems && elems[key] == old(elems[key])
    modifies Repr
// </vc-spec>
// <vc-code>
{
  var b := bucket(k, data.Length);
  var old_list := data[b];
  var found := list_find(k, old_list);
  
  // Use valid_data to establish connection between elems and data
  assert valid_data(k, old(data[b]), old(elems), old(data));
  
  data[b] := list_remove(k, old_list);
  
  match found {
    case None => 
      // k was not in the hashtable
      assert forall v :: !mem((k,v), old_list);
      // From valid_data, if k were in elems, there would be some v with mem((k,v), old_list)
      // But there isn't, so k !in elems
      assert k !in old(elems);
      elems := old(elems);
    case Some(v) => 
      // k was in the hashtable with value v
      assert mem((k,v), old_list);
      // From valid_data, this means k in elems and elems[k] == Some(v)
      assert k in old(elems) && old(elems)[k] == Some(v);
      elems := map key | key in old(elems) && key != k :: old(elems)[key];
      if size > 0 {
        size := size - 1;
      }
  }
  
  // Prove that RepInv holds
  assert this in Repr && data in Repr && data.Length > 0;
  
  // Prove valid_hash for all buckets
  forall i | 0 <= i < data.Length
    ensures valid_hash(data, i)
  {
    if i == b {
      // For the modified bucket
      forall k', v' | mem((k',v'), data[i])
        ensures bucket(k', data.Length) == i
      {
        assert mem((k',v'), list_remove(k, old_list));
        assert mem((k',v'), old_list) && k != k';
        // Since old valid_hash held for old_list, and k' was in old_list, bucket(k', data.Length) == i
        assert bucket(k', data.Length) == i;
      }
    } else {
      // Other buckets unchanged
      assert data[i] == old(data[i]);
    }
  }
  
  // Prove valid_data
  forall k', v' 
    ensures valid_data(k', v', elems, data)
  {
    var bucket_k' := bucket(k', data.Length);
    
    if k' == k {
      // k is no longer in elems
      assert k !in elems;
      assert !mem((k,v'), data[bucket_k']);
    } else {
      // k' != k, so its status should be preserved
      if bucket_k' == b {
        // Same bucket as removed key
        if found.Some? {
          assert (k' in elems && elems[k'] == Some(v')) <==> (k' in old(elems) && old(elems[k']) == Some(v'));
        } else {
          assert elems == old(elems);
          assert (k' in elems && elems[k'] == Some(v')) <==> (k' in old(elems) && old(elems[k']) == Some(v'));
        }
        assert (k' in old(elems) && old(elems[k']) == Some(v')) <==> mem((k',v'), old_list);
        assert mem((k',v'), old_list) && k != k' <==> mem((k',v'), data[bucket_k']);
      } else {
        // Different bucket, unchanged
        assert data[bucket_k'] == old(data[bucket_k']);
        if found.Some? {
          assert (k' in elems && elems[k'] == Some(v')) <==> (k' in old(elems) && old(elems[k']) == Some(v'));
        } else {
          assert elems == old(elems);
        }
      }
    }
  }
}
// </vc-code>

}