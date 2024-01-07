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

#focus-slide[
    = $ert$ in a nutshell
]

#slide[
    ...
]

#focus-slide[
    = The Implementation
]

#slide[
    ...
]

#slide[
    = History
    ...
]

#slide[
    = Using Lean Poorly
    ...
]

#slide[
    = `dsimp` and the OOM killer
    ...
]

#slide[
    = Using Lean (a little) Better
    ...
]

#slide[
    = Future: Verified Interpreter w/ `lean-sys`
    ...
]

#focus-slide[
    = Adding Nothing to HOL
]

#slide[
    ...
]

#focus-slide[
    = The Isotope Project
]

#slide[
    ...
]

// #slide[
//     #only("3-")[
//         ```haskell
//         -- the output length is the sum of the input lengths
//         ```
//     ]
//     #one-by-one[
//         ```haskell
//         append [] ys = ys
//         ```
//     ][
//         ```haskell
//         append (x:xs) ys = x:(append xs ys)
//         ```
//     ]
// ]

// #let gst(x) = text(gray.darken(30%), x)

// #slide[
//     ```haskell
//     -- the output length is the sum of the input lengths
//     ```
//     #only("1-")[
//         ```
//         append : ∀m n: ℕ -> Array A m -> Array A n -> Array A (m + n)
//         ```
//     ]
//     #only("3-")[
//         `append `#gst(`0 n {`)`[]`#gst(`, p} {`)`ys`#gst(`, q}`)` = `#gst(`{`)`ys`#gst({
//             only("3", [`, `

//             `   ... : len ys = 0 + n}`]
//             )
//             only("4", [`, `

//             `   trans[len ys =(q) n =(?) 0 + n]}`]
//             )
//             only("5-", [`, `
            
//             `   trans[len ys =(q) n =(β) 0 + n]}`]
//             )
//         })
//     ]

//     #only("6-")[
//         `append `#gst(`(s m) n {`)`(x:xs)`#gst(`, p} {`)`ys`#gst(`, q}`)` = `
//     ]

//     #only("7-")[
//         `   let `#gst(`{`)`zs`#gst(`, r}`)` = append `
//         #gst(`n m {`)`xs`#gst(`, ... : len xs = n} {`)`ys`#gst(`, q}`)
//     ]

//     #only("8-")[
//         `   in `#gst(`{`)`x:zs`#gst(`, ... : len(x:zs) = (s m) + n}`)
//     ]
//     #align(bottom)[
//         #only("2-")[
//             #v(1em)
//             ```haskell
//             Array A n := { l : List A | len l = n }
//             ```
//         ]
//     ]
// ]


// // going to write a signature and implementation which superficially resembles our Agda program
// // I have a type that says ∀m n, it says what it says
// // At this point, want to then give def and can mention that the gray stuff will be explained soon

// #slide[
//     ```
//     |append| : 1 -> 1 -> List |A| -> List |A| -> List |A|
//     ```
//     ```
//     append () () [] ys = ys

//     append () () (x:xs) ys = 
//         let zs = append xs ys 
//         in x:zs
//     ```
// ]

// #slide[
//     ```
//     append : ∀m n: ℕ -> Array A m -> Array A n -> Array A (m + n)
//     ```
//     `append `#gst(`0 n {`)`[]`#gst(`, p} {`)`ys`#gst(`, q}`)` = `#gst(`{`)`ys`#gst([`, `
        
//         `   trans[len ys =(q) n =(β) 0 + n]`]
//     )

//     `append `#gst(`(s m) n {`)`(x:xs)`#gst(`, p} {`)`ys`#gst(`, q}`)` = `

//     `append `#gst(`(s m) n {`)`(x:xs)`#gst(`, p} {`)`ys`#gst(`, q}`)` = `

//     `   let `#gst(`{`)`zs`#gst(`, r}`)` = append `
//     #gst(`n m {`)`xs`#gst(`, ... : len xs = n} {`)`ys`#gst(`, q}`)

//     `   in `#gst(`{`)`x:zs`#gst(`, ... : len(x:zs) = (s m) + n}`)
// ]

// #slide[
//     `append : ∀m n: ℕ -> Array A m -> Array A n -> Array A `#text(red, `(n + m)`)

//     `append `#gst(`0 n {`)`[]`#gst(`, p} {`)`ys`#gst(`, q}`)` = `#gst(`{`)`ys`#gst([`, `
        
//         `   ... : len ys = n + 0]`]
//     )

//     `append `#gst(`(s m) n {`)`(x:xs)`#gst(`, p} {`)`ys`#gst(`, q}`)` = `

//     `   let `#gst(`{`)`zs`#gst(`, r}`)` = append `
//     #gst(`n m {`)`xs`#gst(`, ... : len xs = n} {`)`ys`#gst(`, q}`)

//     `   in `#gst(`{`)`x:zs`#gst(`, ... : len(x:zs) = n + (s m)}`)
// ]

// #slide[
//     `append `#gst(`0 n {`)`[]`#gst(`, p} {`)`ys`#gst(`, q}`)` = `#gst(`{`)`ys`#gst[`, `
        
//         #only("1")[`   ... : len ys = n + 0]`]
//         #only("2-5")[`   trans[len ys =(q) n =(?) n + 0`]
//         #only("6-")[`   trans[len ys =(q) n =(zero-right-id n) n + 0`]
//     ]

//     #gst(align(bottom)[
//         #uncover("3-")[
//             #v(1em)
//             ```
//             zero-right-id : ∀n: ℕ -> n + 0 = n 
//             ```
//         ]
//         #uncover("4-")[
//             ```
//             zero-right-id 0 = β
//             ```
//         ]
//         #uncover("5-")[
//             ```
//             zero-right-id (s n) = trans [
//                 (s n) + 0 =(β) s (n + 0) =(zero-right-id n) (s n)
//             ]
//             ```
//         ]
//     ])
// ]

// #slide[
//     `append : ∀m n: ℕ -> Array A m -> Array A n -> Array A (n + m)`

    
//     `append `#gst(`0 n {`)`[]`#gst(`, p} {`)`ys`#gst(`, q}`)` = `#gst(`{`)`ys`#gst([`, `
        
//         `   trans[len ys =(q) n =(zero-right-id n) n + 0]`]
//     )

//     `append `#gst(`(s m) n {`)`(x:xs)`#gst(`, p} {`)`ys`#gst(`, q}`)` = `

//     `   let `#gst(`{`)`zs`#gst(`, r}`)` = append `
//     #gst(`n m {`)`xs`#gst(`, ... : len xs = n} {`)`ys`#gst(`, q}`)

//     `   in `#gst(`{`)`x:zs`#gst(`, ... : len(x:zs) = n + (s m)}`)

//     #gst(align(bottom)[
//         ```
//         zero-right-id : ∀n: ℕ -> n + 0 = n 
//         ```
//     ])
// ]

// #slide[
//     ```
//     |append| : 1 -> 1 -> List |A| -> List |A| -> List |A|
//     ```
//     ```
//     append () () [] ys = ys

//     append () () (x:xs) ys = 
//         let zs = append xs ys 
//         in x:zs
//     ```
// ]

// #slide(gst[
//     ```
//     mul-comm: ∀{m n: ℕ} -> m * n = n * m
//     ```
//     #only("2-")[
//         ```
//         mul-comm 0 n = trans[0 * n 
//             =(β) 0 =(mul-zero-right n) n * 0]
//         ```
//     ]
//     #only("4-")[
//         ```
//         mul-comm (s m) n = trans[(s m) * n =(β) (m * n) + n 
//             =(mul-comm m (s n)) (n * m) + n
//             =(mul-succ (s n) m) n * (s m)]
//         ```
//     ]
//     #align(bottom)[
//         #uncover("3-")[
//             ```
//             mul-zero-right : ∀n: ℕ -> n * 0 = 0
//             ```
//         ]
//         #uncover("5-")[
//             ```
//             mul-succ : ∀m n: ℕ -> m * (s n) = m * n + m
//             ```
//         ]
//     ]
// ])

// #slide[
//     = Folklore

//     #v(0.5em)

//     #let pro(txt) = align(left, [#text(olive, "✓") #txt])
//     #let con(txt) = align(left, [#text(red, "✗") #txt])

//     #align(center, grid(
//         columns: 2,
//         column-gutter: 6em,
//         row-gutter: 1em,
//         [*Refinement Types*],
//         [*Dependent Types*],
//         only("2-", pro[High automation]),
//         only("3-", con[Low automation]),
//         only("4-", con[Low expressivity]),
//         only("5-", pro[High expressivity]),
//         only("6-", con[Big TCB]),
//         only("7-", pro[Small TCB])
//     ))

//     #only("8-", align(bottom, 
//         cite(<ftrs>, style: "chicago-fullnotes")))
// ]

// #slide[
//   = What we actually implemented
//   ...
//   - $ℕ$, no `List`/`Array`
//   - de-Bruijn indices
//   - No pattern matching; explicit recursors
//     - Reminds me of the equation compiler!
// ]

#focus-slide[
  = Questions?
  
  ---

  #link("mailto:jeg74@cam.ac.uk")[`jeg74@cam.ac.uk`]
]

#bibliography("references.bib")