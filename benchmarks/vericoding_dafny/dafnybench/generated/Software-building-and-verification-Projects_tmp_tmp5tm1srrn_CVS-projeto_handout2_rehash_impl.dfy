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
lemma mem_cons_lemma<T>(x: T, y: T, xs: List<T>)
  ensures mem(x, Cons(y, xs)) <==> (x == y || mem(x, xs))
{
}

lemma valid_hash_preservation_lemma(newData: array<List<(K,V)>>, k: K, v: V, newBucket: int, oldList: List<(K,V)>, newSize: int)
  requires newSize > 0
  requires 0 <= newBucket < newData.Length == newSize
  requires newBucket == bucket(k, newSize)
  requires forall j :: 0 <= j < newSize ==> valid_hash(newData, j)
  ensures forall k',v' :: mem((k',v'), Cons((k,v), oldList)) ==> bucket(k', newSize) == newBucket
{
  forall k', v' | mem((k',v'), Cons((k,v), oldList))
    ensures bucket(k', newSize) == newBucket
  {
    mem_cons_lemma((k',v'), (k,v), oldList);
    if k' == k && v' == v {
      assert bucket(k', newSize) == bucket(k, newSize) == newBucket;
    } else {
      assert mem((k',v'), oldList);
      // Use the fact that valid_hash holds for the bucket
      assert valid_hash(newData, newBucket);
      assert bucket(k', newSize) == newBucket;
    }
  }
}

lemma valid_data_preservation_lemma(k: K, v: V, l: List<(K,V)>, rest: List<(K,V)>, newData: array<List<(K,V)>>, 
                                   i: int, oldSize: int, newSize: int, newBucket: int)
  requires oldSize > 0 && newSize > 0
  requires newData.Length == newSize
  requires l == Cons((k,v), rest)
  requires newBucket == bucket(k, newSize)
  requires 0 <= newBucket < newSize
  requires forall k',v' :: mem((k',v'), l) ==> oldSize > 0 && bucket(k', oldSize) == i
  requires forall k',v' :: (
                           if oldSize > 0 && 0 <= bucket(k', oldSize) < i then
                             valid_data(k',v',elems,newData)
                           else if oldSize > 0 && bucket(k', oldSize) == i then
                             ((k' in elems && elems[k'] == Some(v'))
                              <==> mem((k',v'), l) || mem((k',v'),newData[bucket(k', newSize)]))
                           else if oldSize > 0 then
                             !mem((k',v'),newData[bucket(k', newSize)])
                           else false)
  ensures forall k',v' :: (
                         if oldSize > 0 && 0 <= bucket(k', oldSize) < i then
                           valid_data(k',v',elems,newData)
                         else if oldSize > 0 && bucket(k', oldSize) == i then
                           ((k' in elems && elems[k'] == Some(v'))
                            <==> mem((k',v'), rest) || mem((k',v'),Cons((k,v), newData[bucket(k', newSize)])))
                         else if oldSize > 0 then
                           !mem((k',v'),Cons((k,v), newData[bucket(k', newSize)]))
                         else false)
{
  forall k', v'
    ensures if oldSize > 0 && 0 <= bucket(k', oldSize) < i then
              valid_data(k',v',elems,newData)
            else if oldSize > 0 && bucket(k', oldSize) == i then
              ((k' in elems && elems[k'] == Some(v'))
               <==> mem((k',v'), rest) || mem((k',v'),Cons((k,v), newData[bucket(k', newSize)])))
            else if oldSize > 0 then
              !mem((k',v'),Cons((k,v), newData[bucket(k', newSize)]))
            else false
  {
    if oldSize > 0 && 0 <= bucket(k', oldSize) < i {
      // This case remains unchanged
    } else if oldSize > 0 && bucket(k', oldSize) == i {
      // For elements in bucket i, we need to show the equivalence holds
      mem_cons_lemma((k',v'), (k,v), newData[bucket(k', newSize)]);
      assert mem((k',v'), l) <==> (mem((k',v'), rest) || (k' == k && v' == v));
      if bucket(k', newSize) == newBucket {
        // The assertion is now properly structured
        assert mem((k',v'), Cons((k,v), newData[newBucket])) <==> 
               ((k' == k && v' == v) || mem((k',v'), newData[newBucket]));
      }
    } else if oldSize > 0 {
      // For other buckets, the new element shouldn't appear
      if bucket(k', newSize) == newBucket {
        mem_cons_lemma((k',v'), (k,v), newData[newBucket]);
        assert !mem((k',v'), l);
        assert bucket(k', oldSize) != i;
        assert !mem((k',v'), newData[newBucket]);
        assert !mem((k',v'), Cons((k,v), newData[newBucket])) <==> !(k' == k && v' == v);
        if k' == k && v' == v {
          assert mem((k,v), l);
          assert bucket(k, oldSize) == i;
          assert false;
        }
      }
    }
  }
}
// </vc-helpers>

method rehash(l: List<(K,V)>, newData: array<List<(K,V)>>,i: int, oldSize: int, newSize: int)
    requires newData != data
    requires 0 < oldSize == data.Length
    requires newData.Length == 2 * oldSize == newSize
    requires forall k,v :: mem((k,v), l) ==> bucket(k, oldSize) == i
    requires forall j :: 0 <= j < newSize ==> valid_hash(newData, j)
    requires forall k,v :: (
                           if 0 <= bucket(k, oldSize) < i then
                             valid_data(k,v,elems,newData)
                           else if bucket(k, oldSize) == i then
                             ((k in elems && elems[k] == Some(v))
                              <==> mem((k,v), l) || mem((k,v),newData[bucket(k, newSize)]))
                           else
                             !mem((k,v),newData[bucket(k, newSize)]))
    ensures forall j :: 0 <= j < newSize ==> valid_hash(newData, j)
    ensures forall k,v ::
              (if 0 <= bucket(k, oldSize) <= i then
                valid_data(k,v,elems,newData)
              else
                !mem((k,v),newData[bucket(k, newSize)]))
    modifies newData
    decreases l
// </vc-spec>
// <vc-code>
{
  match l {
    case Nil => 
      // Base case: empty list, nothing to rehash
      return;
    case Cons((k, v), rest) => 
      // Assert that we have positive sizes to satisfy bucket preconditions
      assert newSize > 0;
      assert oldSize > 0;
      
      // Get the new bucket for this key-value pair
      var newBucket := bucket(k, newSize);
      
      // Store old value for proof
      ghost var oldList := newData[newBucket];
      
      // Add this pair to the appropriate bucket in newData
      newData[newBucket] := Cons((k, v), newData[newBucket]);
      
      // Prove that valid_hash is preserved for the modified bucket
      valid_hash_preservation_lemma(newData, k, v, newBucket, oldList, newSize);
      
      // Assert that valid_hash is maintained for all buckets
      assert forall j :: 0 <= j < newSize ==> valid_hash(newData, j);
      
      // Prove the precondition for the recursive call
      valid_data_preservation_lemma(k, v, l, rest, newData, i, oldSize, newSize, newBucket);
      
      // Assert the precondition holds for rest
      assert forall k',v' :: (
                           if 0 <= bucket(k', oldSize) < i then
                             valid_data(k',v',elems,newData)
                           else if bucket(k', oldSize) == i then
                             ((k' in elems && elems[k'] == Some(v'))
                              <==> mem((k',v'), rest) || mem((k',v'),newData[bucket(k', newSize)]))
                           else
                             !mem((k',v'),newData[bucket(k', newSize)]));
      
      // Recursively process the rest of the list
      rehash(rest, newData, i, oldSize, newSize);
  }
}
// </vc-code>

}