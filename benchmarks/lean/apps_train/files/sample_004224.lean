Have you heard about Megamind? Megamind and Metro Man are two aliens who came to earth. Megamind wanted to destroy the earth, while Metro Man wanted to stop him and protect mankind. After a lot of fighting, Megamind finally threw Metro Man up into the sky. Metro Man was defeated and was never seen again. Megamind wanted to be a super villain. He believed that the difference between a villain and a super villain is nothing but presentation. Megamind became bored, as he had nobody or nothing to fight against since Metro Man was gone. So, he wanted to create another hero against whom he would fight for recreation. But accidentally, another villain named Hal Stewart was created in the process, who also wanted to destroy the earth. Also, at some point Megamind had fallen in love with a pretty girl named Roxanne Ritchi. This changed him into a new man. Now he wants to stop Hal Stewart for the sake of his love. So, the ultimate fight starts now.

* Megamind has unlimited supply of guns named Magic-48. Each of these guns has `shots` rounds of magic spells.
* Megamind has perfect aim. If he shoots a magic spell it will definitely hit Hal Stewart. Once hit, it decreases the energy level of Hal Stewart by `dps` units.
* However, since there are exactly `shots` rounds of magic spells in each of these guns, he may need to swap an old gun with a fully loaded one. This takes some time. Let’s call it swapping period. 
* Since Hal Stewart is a mutant, he has regeneration power. His energy level increases by `regen` unit during a swapping period. 
* Hal Stewart will be defeated immediately once his energy level becomes zero or negative. 
* Hal Stewart initially has the energy level of `hp` and Megamind has a fully loaded gun in his hand.
* Given the values of `hp`, `dps`, `shots` and `regen`, find the minimum number of times Megamind needs to shoot to defeat Hal Stewart. If it is not possible to defeat him,  return `-1` instead.

# Example
Suppose, `hp` = 13, `dps` = 4, `shots` = 3 and `regen` = 1. There are 3 rounds of spells in the gun. Megamind shoots all of them. Hal Stewart’s energy level decreases by 12 units, and thus his energy level becomes 1. Since Megamind’s gun is now empty, he will get a new gun and thus it’s a swapping period. At this time, Hal Stewart’s energy level will increase by 1 unit and will become 2. However, when Megamind shoots the next spell, Hal’s energy level will drop by 4 units and will become −2, thus defeating him. So it takes 4 shoots in total to defeat Hal Stewart. However, in this same example if Hal’s regeneration power was 50 instead of 1, it would have been impossible to defeat Hal.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
