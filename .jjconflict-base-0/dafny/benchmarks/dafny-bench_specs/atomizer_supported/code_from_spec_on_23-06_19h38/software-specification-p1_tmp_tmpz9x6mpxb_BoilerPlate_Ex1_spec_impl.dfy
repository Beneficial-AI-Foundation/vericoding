// ATOM 
datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)

// ATOM 
datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)

// ATOM 
function serialise<V>(t : Tree<V>) : seq<Code<V>> 
{
  match t {
    case Leaf(v) => [ CLf(v) ]
    case SingleNode(v, t) => serialise(t) + [ CSNd(v) ]
    case DoubleNode(v, t1, t2) => serialise(t2) + serialise(t1) + [ CDNd(v) ]
  }
}

// Ex 1
// ATOM 
// Ex 1
function deserialiseAux<T>(codes: seq<Code<T>>, trees: seq<Tree<T>>): seq<Tree<T>>
  requires |codes| > 0 || |trees| > 0
  ensures |deserialiseAux(codes, trees)| >= 0
{
  if |codes| == 0 then trees
  else
    match codes[0] {
      case CLf(v) => deserialiseAux(codes[1..], trees + [Leaf(v)])
      case CSNd(v) => if (|trees| >= 1) then deserialiseAux(codes[1..], trees[..|trees|-1] + [SingleNode(v, trees[|trees|-1])]) else trees
      case CDNd(v) => if (|trees| >= 2) then deserialiseAux(codes[1..], trees[..|trees|-2] + [DoubleNode(v, trees[|trees|-1], trees[|trees|-2])]) else trees
    }
}

// ATOM 
function deserialise<T>(s:seq<Code<T>>):seq<Tree<T>>
  requires |s| > 0
{
  deserialiseAux(s, [])
}

// Ex 2
//IMPL 
// Ex 2
method testSerializeWithASingleLeaf()
{
  var tree := Leaf(42);
  var serialized := serialise(tree);
  /* code modified by LLM (iteration 1): Direct assertion using definition expansion */
  assert serialized == [CLf(42)];
}

//IMPL 
method testSerializeNullValues()
{
  var tree := Leaf(0);
  var serialized := serialise(tree);
  /* code modified by LLM (iteration 1): Direct assertion using definition expansion */
  assert serialized == [CLf(0)];
}

//IMPL 
method testSerializeWithAllElements()
{
  var leaf1 := Leaf(1);
  var leaf2 := Leaf(2);
  var singleNode := SingleNode(3, leaf1);
  var doubleNode := DoubleNode(4, singleNode, leaf2);
  var serialized := serialise(doubleNode);
  
  /* code modified by LLM (iteration 1): Step-by-step verification using serialise definition */
  assert serialise(leaf1) == [CLf(1)];
  assert serialise(leaf2) == [CLf(2)];
  assert serialise(singleNode) == serialise(leaf1) + [CSNd(3)] == [CLf(1)] + [CSNd(3)] == [CLf(1), CSNd(3)];
  assert serialise(doubleNode) == serialise(leaf2) + serialise(singleNode) + [CDNd(4)];
  assert serialise(doubleNode) == [CLf(2)] + [CLf(1), CSNd(3)] + [CDNd(4)];
  assert serialise(doubleNode) == [CLf(2), CLf(1), CSNd(3), CDNd(4)];
  assert serialized == [CLf(2), CLf(1), CSNd(3), CDNd(4)];
}

// Ex 3 
//IMPL 
// Ex 3 
method testDeseraliseWithASingleLeaf() {
  var codes := [CLf(42)];
  var deserialized := deserialise(codes);
  /* code modified by LLM (iteration 1): Step-by-step verification using function definitions */
  assert deserialized == deserialiseAux([CLf(42)], []);
  assert deserialiseAux([CLf(42)], []) == deserialiseAux([], [] + [Leaf(42)]);
  assert deserialiseAux([], [Leaf(42)]) == [Leaf(42)];
  assert deserialized == [Leaf(42)];
}

//IMPL 
method testDeserializeWithASingleNode()
{
  var codes := [CLf(1), CSNd(2)];
  var deserialized := deserialise(codes);
  /* code modified by LLM (iteration 1): Detailed step-by-step verification */
  assert deserialized == deserialiseAux([CLf(1), CSNd(2)], []);
  assert deserialiseAux([CLf(1), CSNd(2)], []) == deserialiseAux([CSNd(2)], [] + [Leaf(1)]);
  assert deserialiseAux([CSNd(2)], [Leaf(1)]) == deserialiseAux([], [Leaf(1)][..|[Leaf(1)]|-1] + [SingleNode(2, [Leaf(1)][|[Leaf(1)]|-1])]);
  assert [Leaf(1)][..|[Leaf(1)]|-1] == [Leaf(1)][..0] == [];
  assert [Leaf(1)][|[Leaf(1)]|-1] == [Leaf(1)][0] == Leaf(1);
  assert deserialiseAux([], [] + [SingleNode(2, Leaf(1))]) == [SingleNode(2, Leaf(1))];
  assert deserialized == [SingleNode(2, Leaf(1))];
}

//IMPL 
method testDeserialiseWithAllElements()
{
  var codes := [CLf(2), CLf(1), CSNd(3), CDNd(4)];
  var deserialized := deserialise(codes);
  var expected := DoubleNode(4, SingleNode(3, Leaf(1)), Leaf(2));
  
  /* code modified by LLM (iteration 1): Detailed step-by-step verification with intermediate assertions */
  assert deserialized == deserialiseAux([CLf(2), CLf(1), CSNd(3), CDNd(4)], []);
  
  // Step 1: Process CLf(2)
  assert deserialiseAux([CLf(2), CLf(1), CSNd(3), CDNd(4)], []) == 
         deserialiseAux([CLf(1), CSNd(3), CDNd(4)], [] + [Leaf(2)]);
  
  // Step 2: Process CLf(1)
  assert deserialiseAux([CLf(1), CSNd(3), CDNd(4)], [Leaf(2)]) == 
         deserialiseAux([CSNd(3), CDNd(4)], [Leaf(2)] + [Leaf(1)]);
  
  // Step 3: Process CSNd(3)
  var trees_after_2_leaves := [Leaf(2), Leaf(1)];
  assert |trees_after_2_leaves| >= 1;
  assert trees_after_2_leaves[..|trees_after_2_leaves|-1] == [Leaf(2), Leaf(1)][..1] == [Leaf(2)];
  assert trees_after_2_leaves[|trees_after_2_leaves|-1] == [Leaf(2), Leaf(1)][1] == Leaf(1);
  assert deserialiseAux([CSNd(3), CDNd(4)], [Leaf(2), Leaf(1)]) == 
         deserialiseAux([CDNd(4)], [Leaf(2)] + [SingleNode(3, Leaf(1))]);
  
  // Step 4: Process CDNd(4)
  var trees_after_single := [Leaf(2), SingleNode(3, Leaf(1))];
  assert |trees_after_single| >= 2;
  assert trees_after_single[..|trees_after_single|-2] == [Leaf(2), SingleNode(3, Leaf(1))][..0] == [];
  assert trees_after_single[|trees_after_single|-1] == [Leaf(2), SingleNode(3, Leaf(1))][1] == SingleNode(3, Leaf(1));
  assert trees_after_single[|trees_after_single|-2] == [Leaf(2), SingleNode(3, Leaf(1))][0] == Leaf(2);
  assert deserialiseAux([CDNd(4)], [Leaf(2), SingleNode(3, Leaf(1))]) == 
         deserialiseAux([], [] + [DoubleNode(4, SingleNode(3, Leaf(1)), Leaf(2))]);
  
  // Final step
  assert deserialiseAux([], [DoubleNode(4, SingleNode(3, Leaf(1)), Leaf(2))]) == 
         [DoubleNode(4, SingleNode(3, Leaf(1)), Leaf(2))];
  
  assert expected == DoubleNode(4, SingleNode(3, Leaf(1)), Leaf(2));
  assert deserialized == [expected];
}

// Ex 4 
// ATOM 
// Ex 4 
lemma SerialiseLemma<V>(t: Tree<V>)
  ensures deserialise(serialise(t)) == [t]
{
  calc{
    deserialise(serialise(t));
    ==
    deserialise(serialise(t) + []);
    ==
    deserialiseAux(serialise(t) + [], []);
    == { DeserialisetAfterSerialiseLemma(t, [], []); }
    deserialiseAux([],[] + [t]);
    ==
    deserialiseAux([],[t]);
    == 
    [t];
  }
}

// ATOM 
lemma DeserialisetAfterSerialiseLemma<T> (t : Tree<T>, cds : seq<Code<T>>, ts : seq<Tree<T>>) 
  ensures deserialiseAux(serialise(t) + cds, ts) == deserialiseAux(cds, ts + [t])
  {
    match t{
      case Leaf(x) =>
        calc{
          deserialiseAux(serialise(t) + cds, ts);
          ==
            deserialiseAux([CLf(x)] + cds, ts);
          == 
            deserialiseAux(cds, ts + [Leaf(x)]);
          == 
            deserialiseAux(cds, ts + [t]);
        }
      case SingleNode(x,t1) =>
        calc{
          deserialiseAux(serialise(t) + cds, ts);
          ==
            deserialiseAux( serialise(t1) + [CSNd(x)] + cds ,ts); 
          ==
            deserialiseAux((serialise(t1) + [CSNd(x)] + cds),ts);
          == { DeserialisetAfterSerialiseLemma(t1 , [ CSNd(x) ], ts); }
            deserialiseAux(serialise(t1)+ [CSNd(x)]  + cds, ts );
          ==
            deserialiseAux( ([CSNd(x)] + cds), ts + [ t1 ]);
          == 
            deserialiseAux(cds, ts + [SingleNode(x,t1)]);
          == 
            deserialiseAux(cds, ts + [t]); 
        }
      case DoubleNode(x,t1,t2) =>
        calc{
          deserialiseAux(serialise(t) + cds, ts);
          ==
            deserialiseAux(serialise(t2) + serialise(t1) + [CDNd(x)] + cds ,ts); 
          ==
            deserialiseAux(serialise(t2) + (serialise(t1) + [CDNd(x)] + cds),ts);
          == { DeserialisetAfterSerialiseLemma(t2, serialise(t1) + [ CDNd(x) ], ts); }
            deserialiseAux(serialise(t1)+ [CDNd(x)]  + cds, ts + [ t2 ]);
          ==
            deserialiseAux(serialise(t1) + ([CDNd(x)] + cds), ts + [ t2 ]);
          == { DeserialisetAfterSerialiseLemma(t1, [ CDNd(x) ] + cds, ts + [ t2 ]); }
            deserialiseAux([ CDNd(x) ] + cds, (ts + [ t2 ]) + [t1]);
          ==
            deserialiseAux([ CDNd(x) ] + cds, ts + [t2, t1]);
          == 
            deserialiseAux([CDNd(x)] + cds, ts + [t2 , t1]);
          == 
            deserialiseAux(cds, ts + [DoubleNode(x,t1,t2)]); 
          == 
            deserialiseAux(cds, ts + [t]);
        }
    }
  }