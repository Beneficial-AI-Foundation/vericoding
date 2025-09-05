Just another day in the world of Minecraft, Steve is working on his new project -- building a beacon pyramid in front of his house.

![Beacon pyramid](http://www.minecraft101.net/reference/images/beacon_pyramid_thb.jpg)

Steve has already obtained the beacon (the glass wrapped blue thingy on the top), he just needs to build the pyramid. Each level of the pyramid is built using one of the following four kinds of block: gold, diamond, emerald, and iron. Since these four kinds of blocks are relatively hard to collect, Steve needs to know exactly how many of each kind is required to build a pyramid of level N.

Assume that the top level of the pyramid uses gold blocks, the second level uses diamond blocks, the third level uses emerald blocks, the fourth level uses iron blocks, and the fifth level uses gold blocks, etc. (if you are a Minecraft player, you know it's not neccessary the right way to build the pyramid. Let's just assume it is for the sake of this kata ;-))

Implement a function that takes one argument which is the number of levels of the pyramid, and returns an object of the form: `{total: 9, gold: 9, diamond: 0, emerald: 0, iron: 0}`.

---

To all the Minecraft players out there: 
feel free to expand this series or let me know if you have any ideas related to Minecraft that can be turned into codewars puzzles. Some ideas I have that might potentially be turned into katas:

* distance traveled in real world vs. in Nether
* shortest path problems related to mining diamonds/gold/goodies that appears in different levels under ground
* growth of animal population from breeding
* redstone stuff?!

If you do end up expanding this series, please send me a link of your kata so I can check it out and include a link to your kata here :-)

* [Minecraft Series #2: Minimum amount of fuel needed to get some iron ingots](https://www.codewars.com/kata/minecraft-series-number-2-minimum-amount-of-fuel-needed-to-get-some-iron-ingots/ruby)
* [Minecraft Series #3: Lava is amazing! ](https://www.codewars.com/kata/583a23d40cf946ec380002c2)
* [Minecraft Series #4: Lava is amazing, however...](https://www.codewars.com/kata/583a6b0b171f3a3c3f0003e3)

def blocks_to_collect (level : Nat) : BlockCount :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded