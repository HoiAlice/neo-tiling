// Dominance relaxation of the minimal perturbation problem, without an optimization
// solver: branch and bound over the coordinate that breaks each conflicting pair, with
// exact isotonic regressions under the loss pi(p, q) = max(q/p, p/q) - 1 in the nodes
// (notes, Theorem "разложение").
//
// Isotonic regression: in u = ln q the loss of index t is f_t(u) = exp|u - a_t| - 1,
// a_t = ln p_t, strictly convex. On a set V with order constraints u_t <= u_s the
// solution is found by recursive thresholding (Hochbaum-Queyranne): theta = the
// minimizer of sum_{t in V} f_t (one block), and the indices with u*_t > theta form the
// minimal upper set minimizing sum f'_t(theta+) (a maximum closure, one min cut). The two
// parts are solved recursively; if nothing is above theta, the maximal upper set with
// the left derivatives gives the indices equal to theta.
//
// Input (stdin):  T d m, then T rows of d positive prices, then m conflicting pairs
//                 "t s" (y_t > y_s: q_t must not strictly dominate q_s).
//                 Optional time limit (seconds) as the 4th number of the first line.
//                 Optional extra clauses: K, then per clause the number of options and
//                 per option "i c t1 s1 ... tc sc" (constraints u_t <= u_s in
//                 coordinate i). With extra clauses for the "pure" blocking of pairs the
//                 problem is a restriction of the cut master: its weakly solvable
//                 optima give upper bounds.
// Output:         lower_bound best nodes finished, then T rows of d prices of the best
//                 point.

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <functional>
#include <limits>
#include <memory>
#include <queue>
#include <utility>
#include <vector>

namespace {

using Pair = std::pair<int, int>;  // (t, s): u_t <= u_s

double loss(double u, double a) { return std::exp(std::fabs(u - a)) - 1.0; }

// right (side = +1) or left (side = -1) derivative of exp|u - a|
double deriv(double u, double a, int side) {
  if (u > a) return std::exp(u - a);
  if (u < a) return -std::exp(a - u);
  return side > 0 ? 1.0 : -1.0;
}

// minimizer of sum_t exp|u - a_t| over t in V: the zero of a monotone subgradient
double block_min(const std::vector<int>& V, const std::vector<double>& a) {
  double lo = std::numeric_limits<double>::infinity(), hi = -lo;
  for (int t : V) lo = std::min(lo, a[t]), hi = std::max(hi, a[t]);
  for (int it = 0; it < 200 && hi - lo > 1e-15; ++it) {
    double mid = 0.5 * (lo + hi), g = 0;
    for (int t : V) g += deriv(mid, a[t], +1);
    if (g > 0) hi = mid; else lo = mid;
  }
  return 0.5 * (lo + hi);
}

// Small max-flow (Edmonds-Karp) on dense capacities.
struct Flow {
  int n;
  std::vector<std::vector<double>> cap;
  explicit Flow(int n_) : n(n_), cap(n_, std::vector<double>(n_, 0.0)) {}
  void run(int s, int t) {
    while (true) {
      std::vector<int> prev(n, -1);
      prev[s] = s;
      std::queue<int> q;
      q.push(s);
      while (!q.empty() && prev[t] < 0) {
        int v = q.front();
        q.pop();
        for (int w = 0; w < n; ++w)
          if (prev[w] < 0 && cap[v][w] > 1e-14) prev[w] = v, q.push(w);
      }
      if (prev[t] < 0) return;
      double f = std::numeric_limits<double>::infinity();
      for (int v = t; v != s; v = prev[v]) f = std::min(f, cap[prev[v]][v]);
      for (int v = t; v != s; v = prev[v]) cap[prev[v]][v] -= f, cap[v][prev[v]] += f;
    }
  }
  std::vector<bool> reach_from(int s) const {  // residual reachability
    std::vector<bool> seen(n, false);
    std::vector<int> st{s};
    seen[s] = true;
    while (!st.empty()) {
      int v = st.back();
      st.pop_back();
      for (int w = 0; w < n; ++w)
        if (!seen[w] && cap[v][w] > 1e-14) seen[w] = true, st.push_back(w);
    }
    return seen;
  }
  std::vector<bool> reach_to(int t) const {
    std::vector<bool> seen(n, false);
    std::vector<int> st{t};
    seen[t] = true;
    while (!st.empty()) {
      int v = st.back();
      st.pop_back();
      for (int w = 0; w < n; ++w)
        if (!seen[w] && cap[w][v] > 1e-14) seen[w] = true, st.push_back(w);
    }
    return seen;
  }
};

// Upper set U of V (t in U, (t, s) a constraint => s in U) minimizing sum_{U} g_t.
// minimal = true: the minimal minimizer, else the maximal one.
std::vector<bool> best_upper_set(const std::vector<int>& V, const std::vector<Pair>& cons,
                                 const std::vector<double>& g, bool minimal, int T) {
  int n = (int)V.size(), S = n, Tt = n + 1;
  std::vector<int> pos(T, -1);
  for (int k = 0; k < n; ++k) pos[V[k]] = k;
  Flow F(n + 2);
  const double inf = 1e18;
  for (int k = 0; k < n; ++k) {
    // closure maximizing sum of -g: source side = U
    if (g[V[k]] < 0) F.cap[S][k] += -g[V[k]];
    else F.cap[k][Tt] += g[V[k]];
  }
  for (auto [t, s] : cons)
    if (pos[t] >= 0 && pos[s] >= 0) F.cap[pos[t]][pos[s]] = inf;
  F.run(S, Tt);
  std::vector<bool> in(T, false);
  if (minimal) {
    auto r = F.reach_from(S);
    for (int k = 0; k < n; ++k) in[V[k]] = r[k];
  } else {
    auto r = F.reach_to(Tt);
    for (int k = 0; k < n; ++k) in[V[k]] = !r[k];
  }
  return in;
}

// Threshold theorem (Hochbaum-Queyranne): for the whole order, {t | u*_t > theta} is the
// minimal upper set minimizing sum f'_t(theta+), and {t | u*_t >= theta} the maximal one
// minimizing sum f'_t(theta-). V holds the indices with u* in (lo, hi]; the interval is
// split at theta (the block minimizer of V, or the midpoint when that makes no progress).
void iso_rec(const std::vector<int>& V, double lo, double hi, const std::vector<int>& all,
             const std::vector<double>& a, const std::vector<Pair>& cons,
             std::vector<double>& u, int T, int depth) {
  if (V.empty()) return;
  double theta = block_min(V, a);
  if (hi - lo < 1e-14 || depth > 400) {
    theta = std::min(std::max(theta, lo), hi);
    for (int t : V) u[t] = theta;
    return;
  }
  if (!(theta > lo && theta < hi) || depth % 2 == 1) theta = 0.5 * (lo + hi);
  std::vector<double> g(T);
  for (int t = 0; t < T; ++t) g[t] = deriv(theta, a[t], +1);
  auto above = best_upper_set(all, cons, g, true, T);
  std::vector<int> U, L;
  for (int t : V) (above[t] ? U : L).push_back(t);
  if (!U.empty()) iso_rec(U, theta, hi, all, a, cons, u, T, depth + 1);
  if (L.empty()) return;
  for (int t = 0; t < T; ++t) g[t] = deriv(theta, a[t], -1);
  auto atleast = best_upper_set(all, cons, g, false, T);
  std::vector<int> B;
  for (int t : L) {
    if (atleast[t]) u[t] = theta;  // u*_t >= theta and <= theta
    else B.push_back(t);
  }
  iso_rec(B, lo, theta, all, a, cons, u, T, depth + 1);
}

// isotonic regression: returns the loss, fills u
double isotonic(const std::vector<double>& a, const std::vector<Pair>& cons,
                std::vector<double>& u) {
  int T = (int)a.size();
  std::vector<int> V(T);
  for (int t = 0; t < T; ++t) V[t] = t;
  u.assign(T, 0.0);
  double lo = *std::min_element(a.begin(), a.end()) - 1e-9;
  double hi = *std::max_element(a.begin(), a.end());
  iso_rec(V, lo, hi, V, a, cons, u, T, 0);
  double total = 0;
  for (int t = 0; t < T; ++t) total += loss(u[t], a[t]);
  return total;
}

struct Option {
  int coord;
  std::vector<Pair> cons;  // u_t <= u_s in coordinate `coord`
};

struct Node {
  double bound;
  std::vector<std::vector<Pair>> fixed;   // per coordinate
  std::vector<std::vector<double>> u;     // per coordinate solution
  std::vector<double> value;              // per coordinate loss
};

struct Cmp {
  bool operator()(const std::shared_ptr<Node>& x, const std::shared_ptr<Node>& y) const {
    return x->bound > y->bound;
  }
};

}  // namespace

int main() {
  int T, d, m;
  double limit = 600;
  if (std::scanf("%d %d %d", &T, &d, &m) != 3) return 1;
  char c = std::getchar();
  if (c == ' ') { double x; if (std::scanf("%lf", &x) == 1) limit = x; }
  std::vector<std::vector<double>> a(d, std::vector<double>(T));
  for (int t = 0; t < T; ++t)
    for (int i = 0; i < d; ++i) { double p; std::scanf("%lf", &p); a[i][t] = std::log(p); }
  // Every requirement is a clause: some option holds; an option is a set of order
  // constraints u_t <= u_s in one coordinate. A conflicting pair (t, s) is the clause
  // with the d options {(t, s)} in coordinate i.
  std::vector<std::vector<Option>> clauses;
  for (int k = 0; k < m; ++k) {
    int t, s;
    std::scanf("%d %d", &t, &s);
    std::vector<Option> cl;
    for (int i = 0; i < d; ++i) cl.push_back({i, {{t, s}}});
    clauses.push_back(cl);
  }
  int extra = 0;
  if (std::scanf("%d", &extra) == 1)
    for (int k = 0; k < extra; ++k) {
      int nopt;
      std::scanf("%d", &nopt);
      std::vector<Option> cl(nopt);
      for (auto& op : cl) {
        int c;
        std::scanf("%d %d", &op.coord, &c);
        op.cons.resize(c);
        for (auto& [t, s] : op.cons) std::scanf("%d %d", &t, &s);
      }
      clauses.push_back(cl);
    }

  auto start = std::chrono::steady_clock::now();
  auto elapsed = [&] {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
  };
  auto root = std::make_shared<Node>();
  root->fixed.assign(d, {});
  root->u.assign(d, {});
  root->value.assign(d, 0.0);
  root->bound = 0;
  for (int i = 0; i < d; ++i) {
    root->value[i] = isotonic(a[i], root->fixed[i], root->u[i]);
    root->bound += root->value[i];
  }
  std::priority_queue<std::shared_ptr<Node>, std::vector<std::shared_ptr<Node>>, Cmp> heap;
  heap.push(root);
  double best = std::numeric_limits<double>::infinity();
  std::shared_ptr<Node> best_node;
  long nodes = 0;
  bool finished = true;
  const double tol = 1e-10;
  while (!heap.empty()) {
    if (elapsed() > limit) { finished = false; break; }
    auto node = heap.top();
    heap.pop();
    if (node->bound >= best - tol) continue;
    ++nodes;
    // the most violated clause: violation = min over options of the largest gap
    double worst = tol;
    int pick = -1;
    for (int k = 0; k < (int)clauses.size(); ++k) {
      double viol = std::numeric_limits<double>::infinity();
      for (const auto& op : clauses[k]) {
        double g = -std::numeric_limits<double>::infinity();
        for (auto [t, s] : op.cons) g = std::max(g, node->u[op.coord][t] - node->u[op.coord][s]);
        viol = std::min(viol, g);
      }
      if (viol > worst) worst = viol, pick = k;
    }
    if (pick < 0) { best = node->bound; best_node = node; continue; }
    for (const auto& op : clauses[pick]) {
      int i = op.coord;
      auto child = std::make_shared<Node>(*node);
      for (auto pr : op.cons) child->fixed[i].push_back(pr);
      child->value[i] = isotonic(a[i], child->fixed[i], child->u[i]);
      child->bound = 0;
      for (int j = 0; j < d; ++j) child->bound += child->value[j];
      if (child->bound < best - tol) heap.push(child);
    }
  }
  double lower = finished ? best : (heap.empty() ? best : std::min(best, heap.top()->bound));
  std::printf("%.15g %.15g %ld %d\n", lower, best, nodes, finished ? 1 : 0);
  if (best_node)
    for (int t = 0; t < T; ++t) {
      for (int i = 0; i < d; ++i) std::printf("%.17g ", std::exp(best_node->u[i][t]));
      std::printf("\n");
    }
  return 0;
}
