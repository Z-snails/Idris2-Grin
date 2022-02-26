---
marp: true
---

# Idris2 GRIN Backend

---

# GRIN

- 'functional' intermediate representation (IR)
- Simple
- Monadic layout
- Easy to optimise

---

```hs
ffi effectful
    _prim_int_print :: T_Int64 -> T_Unit

add_four add_four.x =
    _prim_int_add add_four.x 4

fact fact.n =
    fact.lt <- _prim_int_le fact.n 1
    case fact.lt of
        #True -> pure 1
        #False ->
            fact.pred <- _prim_int_sub fact.n 1
            fact.res <- fact fact.pred
            _prim_int_mul fact.pred fact.res

grinMain =
    main.result <- fact 10
    _prim_int_print main.result
```

---

# Defunctionalisation

| Idris                 | ANF                        | GRIN                 |
| --------------------- | -------------------------- | -------------------- |
| lambda                | partially applied function | constructor          |
| `(\x, y => x + y)`    | `_prim_add_Int`            | `P2_prim_add_Int`    |
| `(\x, y => x + y) 10` | `_prim_add_Int 10`         | `P1_prim_add_Int 10` |

- requires whole program\*

\* can this requirement be relaxed?

---

# Optimisations

- Many small optimisations/simplifications
- [Heap Points-to](#heap-points-to)
- [Generalised unboxing](#generalised-unboxing)
  - 2 parts

---

# Heap Points-to

- Explicit control flow
- Subset of all closures at each `apply`
- Unboxing closure return values/arguments
- Eliminating higher order control flow

---

```hs
apply fn arg =
    case fn of
        (P1foo x) ->
            foo x arg
        (P2foo) ->
            pure (P1foo arg)

foo foo.x foo.y =
    (CInt foo.x0) <- fetch foo.x
    (CInt foo.y0) <- fetch foo.y
    foo.z <- _prim_int_add foo.x0 foo.y0
    pure (CInt foo.z)

grinMain =
    main.10 <- store (CInt 10)
    main.20 <- store (CInt 20)

    main.x <- pure (P2foo)
    main.y <- apply main.x main.10
    main.z <- apply main.y main.20
    (CInt main.z0) <- pure main.z
    _prim_int_print main.z0
```

---

After inlining `apply`

```
fn.0   -> {P2foo[]}
fn.1   -> {P1foo[{0}]}
```

- Exact constructor is known
- Optimised to linear control flow

```hs
foo foo.x foo.y = -- unchanged

grinMain =
    main.10 <- store (CInt 10)
    main.20 <- store (CInt 20)
    main.x <- pure (P2foo)
    main.y <- pure (P1foo main.10)
    (P1foo x.1) <- pure main.y
    main.z <- foo $ x.1 main.20
    (CInt main.z0) <- pure main.z
    _prim_int_print $ main.z0
```

---

# Generalised unboxing

Unboxing returned values

```diff
plus plus.x plus.y =
    (CInt plus.x0) <- fetch plus.x
    (CInt plus.y0) <- fetch plus.y
    plus.z <- _prim_int_add plus.x0 plus.y0
-    pure (CInt plus.z)
+    pure plus.z

grinMain =
    main.x <- store (CInt 10)
    main.y <- store (CInt 20)
-    main.z <- plus main.x main.y
+    main.z <- do
+        unboxed.CInt.0 <- plus.unboxed main.x main.y
+        pure (CInt unboxed.CInt.0)
    (CInt main.z0) <- pure main.z
    _prim_int_print main.z0
```

---

# Generalised unboxing

Arity raising (splitting arguments)

```diff
plus plus.x plus.y =
-    (CInt plus.x0) <- fetch plus.x
-    (CInt plus.y0) <- fetch plus.y
+    (CInt plus.x0) <- pure (CInt plus.x)
+    (CInt plus.y0) <- pure (CInt plus.y)
    plus.z <- _prim_int_add plus.x0 plus.y0
    pure (CInt plus.z)

grinMain =
    main.x <- store (CInt 10)
    main.y <- store (CInt 20)
-    main.z <- plus main.x main.y
+    (CInt main.x0) <- fetch main.x
+    (CInt main.y0) <- fetch main.y
+    main.z <- plus main.x0 main.y0
    (CInt main.z0) <- pure main.z
    _prim_int_print main.z0
```
