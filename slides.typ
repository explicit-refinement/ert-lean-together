#import "@preview/polylux:0.3.1": *

#import themes.simple: *
#show: simple-theme

#let ert = $λ_sans("ert")$;
#let stlc = $λ_sans("stlc")$;

#title-slide[
  = Explicit Refinement Types
  #v(2em)

  Jad Ghalayini #h(1em)
  Neel Krishnaswami

  University of Cambridge
  
  January 11

  Lean Together 2024 -- Online
]

#slide[
  = Explicit Refinement Types By Example
  ...
]

#slide[
    = Folklore

    #v(0.5em)

    #let pro(txt) = align(left, [#text(olive, "✓") #txt])
    #let con(txt) = align(left, [#text(red, "✗") #txt])

    #align(center, grid(
        columns: 2,
        column-gutter: 6em,
        row-gutter: 1em,
        [*Refinement Types*],
        [*Dependent Types*],
        only("2-", pro[High automation]),
        only("3-", con[Low automation]),
        only("4-", con[Low expressivity]),
        only("5-", pro[High expressivity]),
        only("6-", con[Big TCB]),
        only("7-", pro[Small TCB])
    ))

    #only("8-", align(bottom, 
        cite(<ftrs>, style: "chicago-fullnotes")))
]

#slide[
  = Advantages of Lean w.r.t TCB, automation
  ...
]

#slide[
  = The Formalization Process
  ...
]

#slide[
  = Tactics and Bugs and `dsimp`
  ...
]

#slide[
  = Work on Adding Nothing to HOL?
  ...
]

#slide[
  = Modernizing ERT codebase?
  ...
]

#slide[
  = Questions
  ...
]

#bibliography("references.bib")