#!/usr/bin/env python3
"""Independent finite-model regression for the Aemb canonical-coding identity.

Exhausts all targets of size N <= 5, all source 3-graphs A of size
1 <= m <= min(4,N), all increasing source injections e, and every
fixed prefix n <= m. Retains exactly the cases where e is genuinely
finite aux-type-respecting, including both singleton and pair cuts.

For each retained case this constructs the THREE protected strong
pictures, defines their coupled canonical maps in coordinate order
T2, T1, T0, and verifies both all type-image identities and
    F_I^S(A|i+1) = H|e(i)+1   for every i < m.
This standalone combinatorial model is not a Lean proof.
"""

from collections import Counter
from functools import lru_cache
from itertools import combinations


@lru_cache(None)
def labels(coord, size):
    """Valid increasing edge labels in coordinate T0/T1/T2."""
    return tuple(combinations(range(size), 3 - coord))


def node(coord, level, edges):
    return coord, level, frozenset(edges)


def prefix(x, level):
    return node(x[0], level, (b for b in x[2] if b[-1] < level))


def below(x, y):
    return x[0] == y[0] and x[1] <= y[1] and prefix(y, x[1]) == x


def successor(x, added):
    return node(x[0], x[1] + 1, x[2] | frozenset(added))


def children(x):
    new = [b for b in labels(x[0], x[1] + 1) if b[-1] == x[1]]
    for mask in range(1 << len(new)):
        yield successor(x, (b for j, b in enumerate(new) if mask >> j & 1))


def enumeration(H, cut):
    return node(0, cut, (e for e in H if e[-1] < cut))


def one_type(H, cut, v):
    return node(1, cut, (
        (a, b) for a, b in combinations(range(cut), 2)
        if len({a, b, v}) == 3 and tuple(sorted((a, b, v))) in H
    ))


def aux_type(H, cut, u, v):
    return node(2, cut, (
        (a,) for a in range(cut)
        if len({a, u, v}) == 3 and tuple(sorted((a, u, v))) in H
    ))


def finite_aux_respecting(A, H, e, m):
    for a, b, c in combinations(range(m), 3):
        if ((a, b, c) in A) != ((e[a], e[b], e[c]) in H):
            return False
    for u in range(m):
        for v in range(m):
            for w in range(min(u, v) + 1):
                if (one_type(A, w, u) == one_type(A, w, v)) != (
                    one_type(H, e[w], e[u]) == one_type(H, e[w], e[v])
                ):
                    return False
    pairs = tuple(combinations(range(m), 2))
    for u0, u1 in pairs:
        for v0, v1 in pairs:
            for w in range(min(u0, v0) + 1):
                if (aux_type(A, w, u0, u1) == aux_type(A, w, v0, v1)) != (
                    aux_type(H, e[w], e[u0], e[u1]) ==
                    aux_type(H, e[w], e[v0], e[v1])
                ):
                    return False
    return True


def candidate_picture(A, H, e, m, n, coord):
    E = set()
    for k in range(n):
        labs = labels(coord, k)
        for mask in range(1 << len(labs)):
            E.add(node(coord, k,
                       (b for j, b in enumerate(labs) if mask >> j & 1)))
    for i in range(n, m):
        if coord == 0:
            E.add(enumeration(H, e[i]))
        elif coord == 1:
            for v in range(i, m):
                E.add(one_type(H, e[i], e[v]))
        else:
            for u, v in combinations(range(i, m), 2):
                E.add(aux_type(H, e[i], e[u], e[v]))
    return E


def protected_completion(E, coord, e, m):
    roots = {prefix(x, e[0]) for x in E if x[1] >= e[0]}
    assert len(roots) <= 1, ("incompatible first roots", coord, e)
    root = next(iter(roots), node(coord, e[0], ()))
    layers = [{root}]
    for i in range(m - 1):
        L = e[i + 1]
        next_layer = set()
        for p in layers[-1]:
            for t in children(p):
                guides = {prefix(x, L) for x in E
                          if x[1] >= L and below(t, x)}
                assert len(guides) <= 1, ("ambiguous protected cone", coord, e)
                next_layer.add(next(iter(guides), node(coord, L, t[2])))
        layers.append(next_layer)
    assert E <= set.union(*layers), ("prescribed node lost", coord, e)
    return layers


def canonical_map(layers, coord, e, m, lower=None):
    root = node(coord, 0, ())
    mapping = {root: next(iter(layers[0]))}
    for i in range(m - 1):
        for source, p in list(mapping.items()):
            if source[1] != i:
                continue
            for child in children(source):
                if coord == 2:
                    new_bits = [(e[i],)] if (i,) in child[2] else []
                elif coord == 1:
                    parameter = node(2, i, (
                        (a,) for a, b in child[2] if b == i
                    ))
                    new_bits = [(a, e[i]) for (a,) in lower[parameter][2]]
                else:
                    parameter = node(1, i, (
                        (a, b) for a, b, c in child[2] if c == i
                    ))
                    new_bits = [
                        (a, b, e[i]) for a, b in lower[parameter][2]
                    ]
                t = successor(p, new_bits)
                choices = [q for q in layers[i + 1] if below(t, q)]
                assert len(choices) == 1, ("nonunique canonical lift", coord, e)
                mapping[child] = choices[0]
    return mapping


def verify_case(A, H, e, m, n):
    layers = {
        c: protected_completion(candidate_picture(A, H, e, m, n, c),
                                c, e, m)
        for c in (0, 1, 2)
    }
    maps = {}
    for c in (2, 1, 0):
        maps[c] = canonical_map(layers[c], c, e, m, maps.get(c + 1))

    for i in range(m):
        assert maps[0][enumeration(A, i)] == enumeration(H, e[i])
        parameter = maps[1][one_type(A, i, i)]
        assert parameter == one_type(H, e[i], e[i])
        lifted_prefix = successor(
            maps[0][enumeration(A, i)],
            ((a, b, e[i]) for a, b in parameter[2])
        )
        assert lifted_prefix == enumeration(H, e[i] + 1), (
            "F_I^S coding identity", A, H, e, m, n, i
        )
        for v in range(i, m):
            assert maps[1][one_type(A, i, v)] == one_type(H, e[i], e[v])
        for u, v in combinations(range(i, m), 2):
            assert maps[2][aux_type(A, i, u, v)] == aux_type(
                H, e[i], e[u], e[v]
            )


    # Independent check of F_I^S on the WHOLE finite relative carrier,
    # rather than only along the prescribed g_A source branch. Every
    # compatible finite enumeration B of length j+1 is included.
    I = frozenset(t for t in A if t[-1] < n)
    for j in range(m):
        possible = labels(0, j + 1)
        for bmask in range(1 << len(possible)):
            B = frozenset(
                t for idx, t in enumerate(possible) if bmask >> idx & 1
            )
            if j + 1 < n:
                if B != frozenset(t for t in I if t[-1] < j + 1):
                    continue
            elif frozenset(t for t in B if t[-1] < n) != I:
                continue
            mapped_enum = maps[0][enumeration(B, j)]
            mapped_one = maps[1][one_type(B, j, j)]
            mapped_branch = successor(
                mapped_enum,
                ((a, b, e[j]) for a, b in mapped_one[2])
            )
            if j < n:
                assert mapped_branch == enumeration(B, j + 1), (
                    "relative fixed prefix", A, H, e, m, n, j, B
                )
            else:
                assert prefix(mapped_branch, n) == enumeration(A, n), (
                    "relative carrier not preserved", A, H, e, m, n, j, B
                )



def main():
    total = 0
    counts = Counter()
    for N in range(1, 6):
        target_triples = labels(0, N)
        for hmask in range(1 << len(target_triples)):
            H = frozenset(
                t for j, t in enumerate(target_triples) if hmask >> j & 1
            )
            for m in range(1, min(N, 4) + 1):
                source_triples = labels(0, m)
                for e in combinations(range(N), m):
                    for amask in range(1 << len(source_triples)):
                        A = frozenset(
                            t for j, t in enumerate(source_triples)
                            if amask >> j & 1
                        )
                        if not finite_aux_respecting(A, H, e, m):
                            continue
                        for n in range(m + 1):
                            if any(e[k] != k for k in range(n)):
                                continue
                            verify_case(A, H, e, m, n)
                            counts[(N, m)] += 1
                            total += 1
    assert total == 44592, ("unexpected coverage count", total)
    print("PASS: 44592 finite aux-type-respecting configurations")
    print("Coverage by (target vertices, source vertices):", sorted(counts.items()))


if __name__ == "__main__":
    main()
