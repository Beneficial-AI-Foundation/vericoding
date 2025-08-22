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
// SPEC 

// Ex 2
method testSerializeWithASingleLeaf()
{
}


// SPEC 

method testSerializeNullValues()
{
}


// SPEC 

method testSerializeWithAllElements()
{
}


// Ex 3 

// SPEC 

// Ex 3 

method testDeseraliseWithASingleLeaf() {
}


// SPEC 

method testDeserializeWithASingleNode()
{
}


// SPEC 

method testDeserialiseWithAllElements()
{
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




