"""np_corner.py -- chain windows around the U->V corner of the 25-switch instance (ids from cprime2.out), interval-certified credit tables (all bit patterns)."""
from np_lib import *
E, N = 'eq', 'ne'
cert("corner triple V0,u0,u1", [0, 9, 10], [(0, 9, E, 2), (9, 10, N, 2)])
cert("corner triple V1,V0,u0", [1, 0, 9], [(1, 0, E, 2), (0, 9, E, 2)])
cert("corner 4: V1,V0,u0,u1", [1, 0, 9, 10], [(1, 0, E, 2), (0, 9, E, 2), (9, 10, N, 2)])
cert("corner 4: V0,u0,u1,u2", [0, 9, 10, 11], [(0, 9, E, 2), (9, 10, N, 2), (10, 11, N, 2)])
cert("corner 4: V2,V1,V0,u0", [2, 1, 0, 9], [(2, 1, E, 2), (1, 0, E, 2), (0, 9, E, 2)])
