# Story

Well, here I am stuck in another traffic jam.

*Damn all those courteous people!*

Cars are trying to enter the main road from side-streets somewhere ahead of me and people keep letting them cut in.

Each time somebody is let in the effect ripples back down the road, so pretty soon I am not moving at all.

(Sigh... late again...)

## Visually

The diagram below shows lots of cars all attempting to go North.
* the `a`,`b`,`c`... cars are on the main road with me (`X`)
* the `B` cars and `C` cars are merging from side streets

          |  a  |   
          |  b  | ↑  
  --------+  c  |  
     BBBBBB  d  |   
  --------+  e  |  
          |  f  | ↑
          |  g  |   
  --------+  h  |
      CCCCC  i  |
  --------+  j  | ↑
          |  k  |
          |  l  |
          |  m  |
          |  X  | 

This can be represented as

* `mainRoad` = `"abcdefghijklmX"`
* `sideStreets` = `["","","","BBBBBB","","","","","CCCCC"]`

# Kata Task

Assume every car on the main road will "give way" to 1 car entering from each side street.

Return a string representing the cars (up to and including me) in the order they exit off the top of the diagram.

## Notes

* My car is the only `X`, and I am always on the main road
* Other cars may be any alpha-numeric character (except `X` of course)
* There are no "gaps" between cars
* Assume side streets are always on the left (as in the diagram)
* The `sideStreets` array length may vary but is never more than the length of the main road
* A pre-loaded `Util.display(mainRoad,sideStreets)` method is provided which may help to visualise the data
 * (Util.Display for C#)

## Example
Here are the first few iterations of my example, showing that I am hardly moving at all...

InitialIter 1Iter 2Iter 3Iter 4Iter 5Iter 6Iter 7

      a   
      b
      c  
BBBBBBd   
      e  
      f
      g   
      h
 CCCCCi
      j
      k
      l
      m
      X 

      b   
      c
      d 
 BBBBBB   
      e  
      f
      g   
      h
 CCCCCi
      j
      k
      l
      m
      X

      c   
      d
      B
 BBBBBe
      f  
      g
      h   
      i
  CCCCC
      j
      k
      l
      m
      X

       d
       B
       e
   BBBBB
       f
       g
       h
       i
   CCCCC
       j
       k
       l
       m
       X

     B
     e
     B
 BBBBf
     g
     h
     i
     C
 CCCCj
     k
     l
     m
     X

     e
     B
     f
  BBBB
     g
     h
     i
     C
 CCCCj
     k
     l
     m
     X

     B
     f
     B
  BBBg
     h
     i
     C
     j
  CCCC
     k
     l
     m
     X

     f
     B
     g
   BBB
     h
     i
     C
     j
  CCCC
     k
     l
     m
     X

:-) 

DM

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded