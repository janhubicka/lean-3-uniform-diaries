#!/usr/bin/env python3
"""Exhaustively compare the manuscript's exact capped-meet embedding
definition with the finite selected-cut interface used in Lean.

Enumerates all 3-uniform source hypergraphs A with 1<=m<=4, target
hypergraphs H with m<=N<=5, and increasing injections e:[m]->[N].
For every such candidate, the two embedding predicates must agree.
This is independent finite-model evidence, not a proof of the theorem.
"""

from functools import lru_cache
from itertools import combinations

from check_finite_aux_encoding import (
    aux_type,
    finite_aux_respecting,
    labels,
    one_type,
)


@lru_cache(maxsize=None)
def one_meet(edges, u, v):
    return max(
        w for w in range(min(u, v) + 1)
        if one_type(edges, w, u) == one_type(edges, w, v)
    )


@lru_cache(maxsize=None)
def aux_meet(edges, u0, u1, v0, v1):
    return max(
        w for w in range(min(u0, v0) + 1)
        if aux_type(edges, w, u0, u1) ==
           aux_type(edges, w, v0, v1)
    )


def finite_exact_meet_respecting(A, H, e, m):
    for a, b, c in combinations(range(m), 3):
        if ((a, b, c) in A) != ((e[a], e[b], e[c]) in H):
            return False
    for u in range(m):
        for v in range(m):
            if one_meet(H, e[u], e[v]) != e[one_meet(A, u, v)]:
                return False
    pairs = tuple(combinations(range(m), 2))
    for u0, u1 in pairs:
        for v0, v1 in pairs:
            if aux_meet(H, e[u0], e[u1], e[v0], e[v1]) != e[
                aux_meet(A, u0, u1, v0, v1)
            ]:
                return False
    return True


def main():
    tested = 0
    agreeing = 0
    for N in range(1, 6):
        target_triples = labels(0, N)
        for hmask in range(1 << len(target_triples)):
            H = frozenset(
                t for j, t in enumerate(target_triples)
                if hmask >> j & 1
            )
            for m in range(1, min(4, N) + 1):
                source_triples = labels(0, m)
                for emap in combinations(range(N), m):
                    for amask in range(1 << len(source_triples)):
                        A = frozenset(
                            t for j, t in enumerate(source_triples)
                            if amask >> j & 1
                        )
                        selected = finite_aux_respecting(A, H, emap, m)
                        exact = finite_exact_meet_respecting(A, H, emap, m)
                        if selected != exact:
                            raise AssertionError(
                                ("finite embedding interface mismatch",
                                 N, m, A, H, emap, selected, exact)
                            )
                        tested += 1
                        agreeing += int(selected)
    assert tested > 100_000, ("insufficient coverage", tested)
    print(
        f"PASS: {tested} finite embeddings audited for exact-meet "
        f"vs selected-cut equivalence ({agreeing} respecting)"
    )


if __name__ == "__main__":
    main()
