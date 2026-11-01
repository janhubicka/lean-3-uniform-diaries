#!/usr/bin/env python3
"""Adversarial finite regression for the initial seed in manuscript thm:amend.

Given any enumerated 3-uniform graph H on [0,n), build the proposed
3-marker V/E pre-diary P on [0,n+3):
- preserve every original increasing hyperedge on vertices shifted by 3;
- for each pair u<v of old vertices insert EXACTLY one of
  (1,u+3,v+3), (2,u+3,v+3), according to source LexEarlier H(u,v);
- no other edges, particularly no (0,1,v) / (0,2,v) role edges.

The substantive regression is that the DESTINATION's genuinely
computed LexEarlier on the shifted leaves agrees with the source's.
The test also checks the proposed PROOF DECOMPOSITION: every old
singleton meet shifts numerically by three; when the meet is proper,
the deciding full pair-meet shifts numerically by three as well.
It checks a column-invariance property of the source's true LexEarlier,
under equality of singleton types below the first meet.
This is NOT true by construction alone: new marker edges enter its
singleton and auxiliary types and could hypothetically change the
first-disagreement levels.

Exhaust all H with n<=5, then test a deterministic sample at n=6.
Also check the exact induced leaf reduct, leaf roles, complete V3
marker equivalence and E1--E5 permitted-edge shapes.

This is finite-model evidence, NOT a Lean proof for all countable H.
It does not validate the still-missing thm:amend or the FALSE printed
universal old-cut type preservation in lem:prediary.
"""

from itertools import combinations
import random


def one_meet(edges, u, v):
    """Maximum agreeing singleton-type cut, capped at min(u,v)."""
    for cut in range(min(u, v), -1, -1):
        if all(
            ((a, b, u) in edges) == ((a, b, v) in edges)
            for b in range(cut) for a in range(b)
        ):
            return cut
    raise AssertionError("empty singleton type cut range")


def aux_meet(edges, u, v, x, y):
    """Maximum agreeing auxiliary ordered-pair cut."""
    for cut in range(min(u, x), -1, -1):
        if all(
            ((t, u, v) in edges) == ((t, x, y) in edges)
            for t in range(cut)
        ):
            return cut
    raise AssertionError("empty auxiliary type cut range")


def two_meet(edges, u, v, x, y):
    """Exact full pair-type capped meet as min of the three coordinates."""
    return min(
        aux_meet(edges, u, v, x, y),
        one_meet(edges, u, x),
        one_meet(edges, v, y),
    )


def lex_earlier(edges, a, b):
    """The manuscript's genuine lexicographic comparison, not a proxy."""
    m = one_meet(edges, a, b)
    if a < b and m == a:
        return True
    if not m < min(a, b):
        return False
    q = two_meet(edges, m, a, m, b)
    return (q, m, b) in edges


def construct_seed(n, source):
    """Shift the prescribed leaf graph and add its Devlin pair markers."""
    seed = {(a + 3, b + 3, c + 3) for a, b, c in source}
    for a, b in combinations(range(n), 2):
        first = 1 if lex_earlier(source, a, b) else 2
        seed.add((first, a + 3, b + 3))
    return seed


def check_seed(n, source):
    seed = construct_seed(n, source)
    shifted = {(a + 3, b + 3, c + 3) for a, b, c in source}
    # Exact leaf reduct and hence all old edges AND nonedges.
    assert {e for e in seed if e[0] >= 3} == shifted

    # E4 or E5 only; no role edges so every nonmarker is an actual leaf.
    for x, y, z in seed:
        assert 0 <= x < y < z < n + 3
        assert (x in (1, 2) and 3 <= y) or 3 <= x
    assert not any(e[0] == 0 for e in seed)

    for a, b in combinations(range(n), 2):
        m = one_meet(source, a, b)
        m_shifted = one_meet(seed, a + 3, b + 3)
        assert m_shifted == m + 3, (
            "shifted singleton meet fails", n, sorted(source),
            a, b, m, m_shifted
        )
        # The auxiliary/full pair-meet equality is only asserted
        # for proper source singleton meets, NOT the capped case.
        if m < a:
            q = two_meet(source, m, a, m, b)
            q_shifted = two_meet(seed, m + 3, a + 3, m + 3, b + 3)
            assert q_shifted == q + 3, (
                "proper deciding two-meet shift fails", n,
                sorted(source), a, b, m, q, q_shifted
            )
        # Columns a,b agree in singleton type BELOW m.
        # LexEarlier(t,a/b) uses only tests with middle vertex < t,
        # so the comparison must agree for t <= m and t < a.
        for t in range(m + 1):
            if t < a:
                assert lex_earlier(source, t, a) == lex_earlier(
                    source, t, b
                ), (
                    "LexEarlier column invariance fails", n,
                    sorted(source), a, b, m, t
                )
        src = lex_earlier(source, a, b)
        dst = lex_earlier(seed, a + 3, b + 3)
        assert dst == src, (
            "shifted pre-diary V3 fails",
            n, sorted(source), a, b, src, dst,
            one_meet(seed, a + 3, b + 3),
        )
        assert ((1, a + 3, b + 3) in seed) == dst
        assert ((2, a + 3, b + 3) in seed) == (not dst)
    return len(seed)


def main():
    checked = 0
    for n in range(6):
        triples = tuple(combinations(range(n), 3))
        for mask in range(1 << len(triples)):
            source = frozenset(
                e for i, e in enumerate(triples) if (mask >> i) & 1
            )
            check_seed(n, source)
            checked += 1

    # A bounded deterministic adversarial sample outside the exhaustive
    # range, with edge-dense/sparse configurations all represented.
    rng = random.Random(20261101)
    triples = tuple(combinations(range(6), 3))
    for _ in range(1024):
        mask = rng.getrandbits(len(triples))
        source = frozenset(
            e for i, e in enumerate(triples) if (mask >> i) & 1
        )
        check_seed(6, source)
        checked += 1

    # Sparse/dense and mixed random larger sources exercise
    # nontrivial proper first-meet and pair-meet comparisons.
    for n, samples in [(7, 256), (10, 256), (14, 96)]:
        triples = tuple(combinations(range(n), 3))
        for _ in range(samples):
            p = rng.choice([0.03, 0.14, 0.37, 0.5, 0.72, 0.94])
            source = frozenset(
                e for e in triples if rng.random() < p
            )
            check_seed(n, source)
            checked += 1

    assert checked == 1 + 1 + 1 + 2 + 16 + 1024 + 1024 + 256 + 256 + 96, checked
    print(
        f"PASS: {checked} finite pre-diary seed cases; "
        "true destination LexEarlier, complete V3 and "
        "induced leaf reduct"
    )


if __name__ == "__main__":
    main()
