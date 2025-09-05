# Idea

In the world of graphs exists a structure called "spanning tree". It is unique because it's created not on its own, but based on other graphs. To make a spanning tree out of a given graph you should remove all the edges which create cycles, for example:
```
This can become      this      or      this        or       this

 A                    A                  A                   A
 |\                   |                   \                  |\
 | \       ==>        |                    \                 | \
 |__\                 |__                 __\                |  \
B   C                 B  C               B  C                B  C
```
Each *edge* (line between 2 *vertices*, i.e. points) has a weight, based on which you can build minimum and maximum spanning trees (sum of weights of vertices in the resulting tree is minimal/maximal possible).  
[Wikipedia article](https://en.wikipedia.org/wiki/Spanning_tree) on spanning trees, in case you need it.

___

# Task

You will receive an array like this: `[["AB", 2], ["BC", 4], ["AC", 1]]` which includes all edges of an arbitrary graph and a string `"min"`/`"max"`. Based on them you should get and return a new array which includes only those edges which form a minimum/maximum spanning trees.
```python
edges = [("AB", 2), ("BC", 4), ("AC", 1)]

make_spanning_tree(edges, "min")    ==>    [("AB", 2), ("AC", 1)]
make_spanning_tree(edges, "max")    ==>    [("AB", 2), ("BC", 4)]
```

___

# Notes

* All vertices will be connected with each other
* You may receive cycles, for example - `["AA", n]`
* The subject of the test are these 3 values: number of vertices included, total weight, number of edges, but **you should not return them**, there's a special function which will analyze your output instead

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
