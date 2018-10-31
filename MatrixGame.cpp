#include <bits/stdc++.h>
using namespace std;

struct Timer {
    vector<double> tms;
    clock_t last_clock;
    bool reported;
    void start()
    {
        last_clock = clock();
        reported = false;
    }
    double get()
    {
        return double(clock() - last_clock) / CLOCKS_PER_SEC;
    }
    void pulse()
    {
        clock_t now_clock = clock();
        tms.push_back(double(now_clock - last_clock) / CLOCKS_PER_SEC);
        last_clock = now_clock;
        reported = false;
    }
};

const double eps = 1e-5;
const double inf = 1e8;

inline int dcmp(double x, double y = 0)
{
    x -= y;
    return int(x > eps) - int(x < -eps);
}

typedef vector< vector<double> > constraint_t;

pair<int, double> simplex(int n, int m, constraint_t &a, vector<double> &x);
pair<int, double> simplex2(int n, int m, constraint_t &a, vector<double> &x);

void pivot(int n, int m, constraint_t &a, int p, int q, vector<int> &pos,
           vector<int> &var)
{
    /* pivot p and q */
    double a_qp = -a[q][p];
    for (int i = 0; i <= n; ++i)
        a[q][i] /= a_qp;
    a[q][p] = -1.0 / a_qp;
    for (int i = 0; i <= m; ++i)
        if (i != q) {
            double a_ip = a[i][p];
            for (int j = 0; j <= n; ++j)
                a[i][j] += a_ip * a[q][j];
            a[i][p] = a_ip * a[q][p];
        }

    /* swap position */
    swap(var[p], var[n + q - 1]);
    pos[var[p]] = p;
    pos[var[n + q - 1]] = n + q - 1;
}

bool simplify(int n, int m, constraint_t &a, vector<int> &pos, vector<int> &var)
{
    Timer timer;
    timer.start();
    while (timer.get() < 0.1) {
        int p = -1; // select a variable x_p to move in
        for (int i = 0; i < n; ++i)
            if (dcmp(a[0][i]) > 0) {
                p = i;
                break;
            }
        if (p < 0)
            break;

        int q = -1; // select a variable x_q to move out
        double inc; // increment
        for (int i = 1; i <= m; ++i)
            if (dcmp(a[i][p]) < 0) {
                double _inc = a[i][n] / -a[i][p];
                if (q < 0 || dcmp(inc - _inc) > 0) {
                    q = i;
                    inc = _inc;
                }
            }
        if (q < 0)
            return false;

        pivot(n, m, a, p, q, pos, var);
    }
    return true;
}

/* --- simplex algorithm
 * input:
 *  n -- number of variables
 *  m -- number of constraints
 *  a -- array of coefficients (may change)
 * output:
 *  maximize z = a_{0,n} + \sum_{i=0}^{n-1} a_{0,i} * x_i
 *  with constraints (1<=i<=m):
 *      a_{i,n} + \sum_{j=0}^{n-1} a_{i,j} * x_j >= 0
 *  return pair <type, max_z>
 *  type = 0  : no solution
 *  type = -1 : solution goes to infinity
 *  type = 1  : good solution
 *  answer saved in x[]
 */
pair<int, double> simplex(int n, int m, constraint_t &a, vector<double> &x)
{
    bool fsi = true; // already feasible?
    for (int i = 1; i <= m; ++i)
        if (dcmp(a[i][n]) < 0) {
            fsi = false;
            break;
        }
    if (!fsi)
        return simplex2(n, m, a, x);

    vector<int> pos(n + m); // position of a variable
    vector<int> var(n + m); // what is the variable on a position
    for (int i = 0; i < n + m; ++i)
        var[i] = pos[i] = i;

    if (!simplify(n, m, a, pos, var))
        return make_pair(-1, 0);

    x.resize(n);
    for (int i = 0; i < n; ++i)
        if (pos[i] < n)
            x[i] = 0;
        else
            x[i] = a[pos[i] - n + 1][n];

    return make_pair(1, a[0][n]);
}

pair<int, double> simplex2(int n, int m, constraint_t &a, vector<double> &x)
{
    int pm = -1; // smallest constant
    for (int i = 1; i <= m; ++i)
        if (pm == -1 || a[i][n] < a[pm][n])
            pm = i;

    constraint_t b;
    b.resize(m + 1);
    for (int i = 0; i <= m; ++i)
        b[i].resize(n + 2);

    // add new variable x_n
    fill(b[0].begin(), b[0].end(), 0);
    b[0][n] = -1;
    for (int i = 1; i <= m; ++i) {
        copy(a[i].begin(), a[i].end() - 1, b[i].begin());
        b[i][n + 1] = a[i][n];
        if (dcmp(a[i][n]) < 0)
            b[i][n] = 1;
        else
            b[i][n] = 0;
    }

    vector<int> pos(n + m + 1); // position of a variable
    vector<int> var(n + m + 1); // what is the variable on a position
    for (int i = 0; i <= n + m; ++i)
        var[i] = pos[i] = i;

    pivot(n + 1, m, b, n, pm, pos, var);
    if (!simplify(n + 1, m, b, pos, var)) {
        fprintf(stderr, "simplex error!\n");
        return make_pair(-1, 0);
    }
    if (dcmp(b[0][n + 1]) != 0)
        return make_pair(0, 0);

    int pn = pos[n];
    bool nonbase = true; // x_n is base?
    if (pn >= n + 1) {
        int q = pn - n;
        int p = -1;
        for (int i = 0; i <= n; ++i)
            if (dcmp(b[q][i]) != 0) {
                p = i;
                break;
            }
        if (p == -1) {
            /* eliminate a constraint */
            b.erase(b.begin() + q);
            --m;
            nonbase = false;
        }
        else {
            /* make x_n non-base */
            pivot(n + 1, m, b, p, q, pos, var);
            pn = pos[n];
            nonbase = true;
        }
    }
    /* delete x_n */
    if (nonbase)
        for (int i = 0; i <= m; ++i) {
            for (int j = pn; j <= n; ++j)
                b[i][j] = b[i][j + 1];
            b[i].pop_back();
        }
    for (int i = pn; i < n + m; ++i)
        var[i] = var[i + 1];
    for (int i = 0; i < n + m; ++i)
        if (var[i] > n)
            --var[i];
    var.pop_back();
    for (int i = 0; i < n + m; ++i)
        pos[var[i]] = i;
    pos.pop_back();

    /* build optimizer */
    fill(b[0].begin(), b[0].end(), 0);
    for (int i = 0; i < n; ++i) {
        double fac = a[0][i];
        int p = pos[i];
        if (p < n)
            b[0][p] += fac;
        else {
            int q = p - n + 1;
            for (int j = 0; j <= n; ++j)
                b[0][j] += fac * b[q][j];
        }
    }
    b[0][n] += a[0][n];

    if (!simplify(n, m, b, pos, var))
        return make_pair(-1, 0);

    x.resize(n);
    for (int i = 0; i < n; ++i)
        if (pos[i] < n)
            x[i] = 0;
        else
            x[i] = b[pos[i] - n + 1][n];

    return make_pair(1, b[0][n]);
}

/* return probability to choose each row */
double _matrixGame(const vector<vector<double>> &a, vector<double> &p)
{
    double mina = inf;
    int n = a.size(), m = a[0].size();
    for (int i = 0; i < n; ++i)
        for (int j = 0; j < m; ++j)
            mina = min(mina, a[i][j]);
    constraint_t f;
    /* maximize v */
    vector<double> mx(n + 2, 0);
    mx[n] = 1;
    f.push_back(mx);
    /* \sum p = 1  */
    vector<double> sp(n + 2, 1);
    sp[n] = 0, sp[n + 1] = -1;
    f.push_back(sp);
    for (double &cof : sp)
        cof = -cof;
    f.push_back(sp);
    /* p_i >= 0 */
    /*
    for (int i = 0; i < n; ++i) {
        vector<double> pi(n + 2, 0);
        pi[i] = 1;
        f.push_back(pi);
    }
    */
    /* p^T A_i - v >= 0 */
    for (int i = 0; i < m; ++i) {
        vector<double> tmp(n + 2);
        tmp[n] = -1;
        for (int j = 0; j < n; ++j)
            tmp[j] = a[j][i] - mina;
        f.push_back(tmp);
    }
    pair<int, double> res = simplex(n + 1, m + 2, f, p);
    assert(res.first == 1);
    p.pop_back();
    return res.second + mina;
}

/* return probability to choose each row and column */
double _matrixGame(const vector<vector<double>> &a, vector<double> &p, vector<double> &q)
{
    double ans = _matrixGame(a, p);
    int n = a.size(), m = a[0].size();
    vector<vector<double>> b(m);
    for (int i = 0; i < m; ++i) {
        b[i].resize(n);
        for (int j = 0; j < n; ++j)
            b[i][j] = -a[j][i];
    }
    _matrixGame(b, q);
    return ans;
}

double matrixGame(const vector<vector<double>> &a, vector<double> &p, vector<double> &q)
{
    int n = a.size(), m = a[0].size();
    int n2 = 0, m2 = 0;
    vector<bool> good0(n, true), good1(m, true);
    for (int i = 0; i < n; ++i) {
        bool ok = true;
        for (int j = 0; j < n && ok; ++j)
            if (j != i && good0[j]) {
                bool all_better = true;
                for (int k = 0; k < m && all_better; ++k)
                    if (dcmp(a[i][k], a[j][k]) > 0)
                        all_better = false;
                ok = !all_better;
            }
        good0[i] = ok;
        if (ok)
            ++n2;
    }
    for (int i = 0; i < m; ++i) {
        bool ok = true;
        for (int j = 0; j < m && ok; ++j)
            if (j != i && good1[j]) {
                bool all_better = true;
                for (int k = 0; k < n && all_better; ++k)
                    if (dcmp(a[k][i], a[k][j]) < 0)
                        all_better = false;
                ok = !all_better;
            }
        good1[i] = ok;
        if (ok)
            ++m2;
    }
    vector<double> p0, q0;
    vector<vector<double>> b;
    for (int i = 0; i < n; ++i)
        if (good0[i]) {
            b.push_back(vector<double>());
            for (int j = 0; j < m; ++j)
                if (good1[j])
                    b.back().push_back(a[i][j]);
        }
    double value = _matrixGame(b, p0, q0);
    p.resize(n);
    int ct = 0;
    for (int i = 0; i < n; ++i)
        if (good0[i])
            p[i] = p0[ct++];
        else
            p[i] = 0;
    ct = 0;
    q.resize(m);
    for (int i = 0; i < m; ++i)
        if (good1[i])
            q[i] = q0[ct++];
        else
            q[i] = 0;
    return value;
}


#include "Python.h"

PyObject *MatrixGame_matrixGame(PyObject *self, PyObject *args)
{
    PyObject *arg;
    if (!PyArg_ParseTuple(args, "O", &arg))
        return NULL;
    vector<double> p, q;
    double value;
    int n = PyList_Size(arg);
    if (n == 0)
        return NULL;
    vector<PyObject*> as;
    for (int i = 0; i < n; ++i)
        as.push_back(PyList_GetItem(arg, i));
    int m = PyList_Size(as.front());
    if (m == 0)
        return NULL;
    for (int i = 0; i < n; ++i)
        if (PyList_Size(as[i]) != m)
            return NULL;
    vector<vector<double>> a(n);
    for (int i = 0; i < n; ++i)
        for (int j = 0; j < m; ++j)
            a[i].push_back(PyFloat_AsDouble(PyList_GetItem(as[i], j)));
    value = matrixGame(a, p, q);
    PyObject *po = PyList_New(n), *qo = PyList_New(m);
    for (int i = 0; i < n; ++i)
        PyList_SetItem(po, i, Py_BuildValue("d", p[i]));
    for (int i = 0; i < m; ++i)
        PyList_SetItem(qo, i, Py_BuildValue("d", q[i]));
    return Py_BuildValue("dOO", value, po, qo);
}

PyMethodDef MatrixGameMethods[] = {
    {"matrixGame", MatrixGame_matrixGame, METH_VARARGS},
    {NULL, NULL}
};

struct PyModuleDef modDef = {
    PyModuleDef_HEAD_INIT, 
    "MatrixGame", 
    NULL,
    0,
    MatrixGameMethods
};

PyMODINIT_FUNC PyInit_MatrixGame()
{
    return PyModule_Create(&modDef);
}
