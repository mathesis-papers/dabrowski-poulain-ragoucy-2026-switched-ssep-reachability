import argparse
from collections import Counter, deque
from fractions import Fraction
from itertools import permutations, product
import json
from math import factorial, prod
from pathlib import Path


def compose(first, second):
    return tuple(first[value] for value in second)


def inverse(permutation):
    result = [0] * len(permutation)
    for index, value in enumerate(permutation):
        result[value] = index
    return tuple(result)


def closure(generators, identity, multiply):
    reached = {identity}
    pending = deque([identity])
    while pending:
        current = pending.popleft()
        for generator in generators:
            following = multiply(generator, current)
            if following not in reached:
                reached.add(following)
                pending.append(following)
    return reached


def components(vertices, neighbors):
    unseen = set(vertices)
    result = []
    while unseen:
        first = min(unseen)
        reached = {first}
        unseen.remove(first)
        pending = deque([first])
        while pending:
            current = pending.popleft()
            for following in neighbors(current):
                if following in unseen:
                    unseen.remove(following)
                    reached.add(following)
                    pending.append(following)
        result.append(frozenset(reached))
    return result


def moves(configuration, twist):
    for index in range(len(configuration) - 1):
        changed = list(configuration)
        changed[index], changed[index + 1] = changed[index + 1], changed[index]
        yield tuple(changed)
    changed = list(configuration)
    changed[0] = inverse(twist)[configuration[-1]]
    changed[-1] = twist[configuration[0]]
    yield tuple(changed)


def pair_multiply(first, second):
    return compose(first[0], second[0]), compose(first[1], second[1])


def checked(condition, message):
    if not condition:
        raise AssertionError(message)


def check_profile_fibers(group, derived, configurations, union_components, totals):
    alphabet_size = len(next(iter(group)))
    identity = tuple(range(alphabet_size))
    orbits = components(range(alphabet_size), lambda value: (element[value] for element in group))
    orbit_index = {value: index for index, orbit in enumerate(orbits) for value in orbit}
    basepoints = [min(orbit) for orbit in orbits]
    transporters = {
        value: min(element for element in group if element[basepoints[orbit_index[value]]] == value)
        for value in range(alphabet_size)
    }
    profile_data = {}
    fibers = {}
    for state in configurations:
        profile = tuple(sum(orbit_index[value] == index for value in state) for index in range(len(orbits)))
        if profile not in profile_data:
            stabilizers = {
                element for index, count in enumerate(profile) if count
                for element in group if element[basepoints[index]] == basepoints[index]
            }
            subgroup = closure(derived | stabilizers, identity, compose)
            checked(all(compose(compose(element, member), inverse(element)) in subgroup
                        for element in group for member in subgroup), 'Normal profile subgroup')
            cosets = {element: min(compose(element, member) for member in subgroup) for element in group}
            quotient_order = len(group) // len(subgroup)
            lattice_size = len(state)
            profile_size = factorial(lattice_size) // prod(factorial(count) for count in profile)
            profile_size *= prod(len(orbit)**count for orbit, count in zip(orbits, profile))
            checked(profile_size % quotient_order == 0, 'Integral profile component size')
            profile_data[profile] = cosets, quotient_order, profile_size // quotient_order
        cosets, quotient_order, component_size = profile_data[profile]
        total = identity
        for value in state:
            total = compose(total, transporters[value])
        fibers.setdefault((profile, cosets[total]), set()).add(state)
    checked({frozenset(fiber) for fiber in fibers.values()} == set(union_components),
            'Complete profile and charge fibers equal graph components')
    for profile, (cosets, quotient_order, component_size) in profile_data.items():
        matching = [fiber for (key_profile, charge), fiber in fibers.items() if key_profile == profile]
        checked(len(matching) == quotient_order, 'Profile component count')
        checked(all(len(fiber) == component_size for fiber in matching), 'Profile component sizes')
        totals['profile_count_and_size_cases'] += 1
    totals['profile_charge_graphs'] += 1
    totals['profile_charge_fibers'] += len(fibers)


def verify_families():
    totals = Counter()
    for alphabet_size in range(1, 4):
        identity = tuple(range(alphabet_size))
        for twists in product(permutations(range(alphabet_size)), repeat=3):
            group = closure(twists, identity, compose)
            commutators = {
                compose(compose(compose(first, second), inverse(first)), inverse(second))
                for first, second in product(group, repeat=2)
            }
            derived = closure(commutators, identity, compose)
            transitive = len({element[0] for element in derived}) == alphabet_size
            totals['ordered_triples'] += 1
            for lattice_size in (3, 4):
                configurations = tuple(product(range(alphabet_size), repeat=lattice_size))
                union_components = components(configurations, lambda state: (
                    following for twist in twists for following in moves(state, twist)))
                checked((len(union_components) == 1) == transitive, 'Three-twist criterion')
                check_profile_fibers(group, derived, configurations, union_components, totals)
                totals['configuration_graphs'] += 1
                totals['configurations'] += len(configurations)
    return dict(sorted(totals.items()))


def verify():
    totals = Counter()
    connectivity_counts = Counter()
    maximum_saturation_steps = 0
    exception = None
    for alphabet_size in range(1, 5):
        identity = tuple(range(alphabet_size))
        all_twists = tuple(permutations(range(alphabet_size)))
        for first_twist, second_twist in product(all_twists, repeat=2):
            totals['ordered_twist_pairs'] += 1
            group = closure((first_twist, second_twist), identity, compose)
            commutators = {
                compose(compose(compose(first, second), inverse(first)), inverse(second))
                for first, second in product(group, repeat=2)
            }
            derived = closure(commutators, identity, compose)
            derived_orbits = components(range(alphabet_size), lambda value: (element[value] for element in derived))
            derived_transitive = len(derived_orbits) == 1
            group_transitive = len({element[0] for element in group}) == alphabet_size
            pair_group = closure(
                ((first_twist, inverse(first_twist)), (second_twist, inverse(second_twist))),
                (identity, identity), pair_multiply,
            )
            pair_transitive = len({(element[0][0], element[1][0]) for element in pair_group}) == alphabet_size**2
            for basepoint in range(alphabet_size):
                stabilizer_size = sum(element[0][basepoint] == basepoint and element[1][basepoint] == basepoint for element in pair_group)
                checked((len(pair_group) == alphabet_size**2 * stabilizer_size) == pair_transitive, 'Pair stabilizer criterion')
                totals['pair_stabilizer_equalities'] += 1
            for lattice_size in (2, 3, 4):
                configurations = tuple(product(range(alphabet_size), repeat=lattice_size))
                first_sectors = components(configurations, lambda state: moves(state, first_twist))
                second_sectors = components(configurations, lambda state: moves(state, second_twist))
                union_components = components(configurations, lambda state: (*moves(state, first_twist), *moves(state, second_twist)))
                union_index = {state: component for component in union_components for state in component}
                connected = len(union_components) == 1
                criterion = pair_transitive if lattice_size == 2 else derived_transitive
                checked(connected == criterion, f'Connectivity criterion: {alphabet_size}, {lattice_size}, {first_twist}, {second_twist}')
                totals['configuration_graphs'] += 1
                totals['configurations'] += len(configurations)
                connectivity_counts[f'N={alphabet_size},L={lattice_size}'] += int(connected)
                if lattice_size >= 3 and group_transitive:
                    checked(len(union_components) == len(derived_orbits), 'Abelian charge component count')
                    checked({len(component) for component in union_components} == {alphabet_size**lattice_size // len(derived_orbits)}, 'Abelian charge component sizes')
                    totals['transitive_charge_classifications'] += 1
                if lattice_size >= 3:
                    check_profile_fibers(group, derived, configurations, union_components, totals)
                for sectors, other_sectors in ((first_sectors, second_sectors), (second_sectors, first_sectors)):
                    other_index = {state: sector for sector in other_sectors for state in sector}
                    sector_index = {state: sector for sector in sectors for state in sector}
                    for starting_sector in sectors:
                        probabilities = [Fraction(len(starting_sector & target_sector), len(starting_sector)) for target_sector in other_sectors]
                        checked(sum(probabilities) == 1, 'Branching probability row sum')
                        checked(all((probability > 0) == bool(starting_sector & target_sector) for probability, target_sector in zip(probabilities, other_sectors)), 'Positive branching support')
                        totals['branching_rows'] += 1
                        supported = set(starting_sector)
                        expected = union_index[next(iter(starting_sector))]
                        steps = 0
                        while supported != expected:
                            partition_index = other_index if steps % 2 == 0 else sector_index
                            supported = set().union(*(partition_index[state] for state in supported))
                            steps += 1
                            checked(steps <= 2 * (len(expected) - 1), 'Alternating support bound')
                        maximum_saturation_steps = max(maximum_saturation_steps, steps)
                        totals['alternating_start_sectors'] += 1
                if alphabet_size == 3 and lattice_size == 2 and first_twist == (1, 0, 2) and second_twist == (1, 2, 0):
                    exception = {
                        'N': 3, 'L': 2, 'f_images': list(first_twist), 'g_images': list(second_twist),
                        'H_order': len(group), 'derived_order': len(derived), 'pair_group_order': len(pair_group),
                        'components': [list(map(list, sorted(component))) for component in union_components],
                    }
    checked(exception is not None, 'Two-site example is present')
    return {
        'schema_version': 1,
        'result': 'all exact finite checks passed',
        'scope': {'alphabet_sizes': [1, 2, 3, 4], 'lattice_sizes': [2, 3, 4], 'twists': 'every ordered pair of permutations', 'arithmetic': 'integers and rational numbers'},
        'checks': dict(sorted(totals.items())),
        'three_twist_checks': verify_families(),
        'connected_graphs_by_size': dict(sorted(connectivity_counts.items())),
        'largest_observed_alternating_saturation_steps': maximum_saturation_steps,
        'two_site_example': exception,
        'coverage': {
            'all_parameter_classification': 'written proof in note.tex; pinned Lean declaration linked in note.pdf',
            'finite_checks': 'connectivity, pair stabilizers, branching row sums, alternating supports, transitive charge component counts and sizes',
            'transitive_charge_classification': 'written proof and exact finite checks',
            'general_profile_classification': 'complete charge fibers, counts and sizes for every orbit profile; all pairs for N=1..4 and all triples for N=1..3 at L=3,4',
            'positive_time_support': 'Norris (1997), Theorem 3.2.1; written switching specialization by a nonnegative exponential series in note.tex',
            'fair_schedule_support_bound': 'written proof in note.tex; finite-family graph classification checked for every ordered triple at N=1..3 and L=3,4',
            'periodic_limiting_law': 'written proof in note.tex; finite checks concern support and do not compute convergence rates',
        },
    }


def main():
    parser = argparse.ArgumentParser(description='Exact finite checks for switched twisted exclusion processes')
    parser.add_argument('--output', type=Path)
    arguments = parser.parse_args()
    encoded = json.dumps(verify(), indent=2, sort_keys=True) + '\n'
    if arguments.output:
        arguments.output.write_text(encoded)
    else:
        print(encoded, end='')


if __name__ == '__main__':
    main()
