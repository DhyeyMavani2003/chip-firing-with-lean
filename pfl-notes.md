* I don't understand why we need the Prop and Bool versions of some things. About 20 of these instances.
* Perhaps I should learn how to work with quotient types and use this to properly define a "divisor class" type and define rank of a divisor class etc.
* This would be a pretty big refactor, but: in my opinion a CFDivisor should really include a CFGraph implicitly, rather than it needing to always be provided. But OTOH maybe I could just build such functionality on top of what we have here.

* IN helpers.lean line 382, I need to prove one_chip v \le 0. I should probably just prove that once, and look for other places I needed .

* It might simplify various things to define a partial order structure on divisors, and then write E \ge 0 all the time for being effective.

* Various defns can be shortened by making G implicit (or other arguments). Maybe go throuhg and do so. E.g. ordiv O is better than ordiv G O.

* change definition of q-reduced to just use the notion of legal set-firing.

* Consider removing definition of qed and just sending arount the proposition q_effective D instead. Could make life easier!
