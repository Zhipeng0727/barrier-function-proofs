import numpy as np
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

# ============================================================
# Barrier (explicit horizontal level set)
# ============================================================

def B(x1, x2):
    # B = 1/5 - 1/2(x2 + e^(-x1) - 1)^2 - x1/2 + sin(2x1)/4
    return (
        1.0 / 5.0
        - 0.5 * (x2 + np.exp(-x1) - 1.0) ** 2
        - x1 / 2.0
        + np.sin(2.0 * x1) / 4.0
    )


# ============================================================
# System dynamics and unsafe set (from ex4.py)
# ============================================================

def f(x):
    x1, x2 = x
    dx1 = np.exp(-x1) + x2 - 1.0
    dx2 = -(np.sin(x1)) ** 2
    return np.array([dx1, dx2], dtype=float)


def unsafe_fun(x1, x2):
    # Unsafe set (from ex4.py): (x1 - 0.7)^2 + (x2 + 0.7)^2 - 0.09 <= 0
    return (x1 - 0.7) ** 2 + (x2 + 0.7) ** 2 - 0.09


# ============================================================
# RK4 simulator
# ============================================================

def rk4_step(x, dt):
    k1 = f(x)
    k2 = f(x + 0.5 * dt * k1)
    k3 = f(x + 0.5 * dt * k2)
    k4 = f(x + dt * k3)
    return x + (dt / 6.0) * (k1 + 2 * k2 + 2 * k3 + k4)


def simulate(x0, dt=0.01, T=8.0, box=(-2, 2, -2, 2)):
    x = np.array(x0, dtype=float)
    traj = [x.copy()]
    steps = int(T / dt)
    xmin, xmax, ymin, ymax = box

    for _ in range(steps):
        x = rk4_step(x, dt)
        traj.append(x.copy())
        if not (xmin <= x[0] <= xmax and ymin <= x[1] <= ymax):
            break
    return np.array(traj)


# ============================================================
# Plot style: same as ex3.py (paper-like)
# ============================================================

plt.rcParams.update({
    "font.family": "serif",
    "mathtext.fontset": "cm",
    "font.size": 10,
    "axes.labelsize": 12,
    "axes.titlesize": 12,
    "legend.fontsize": 8.5,
    "xtick.labelsize": 9.5,
    "ytick.labelsize": 9.5,
    "axes.linewidth": 0.9,
    "xtick.direction": "in",
    "ytick.direction": "in",
    "xtick.major.size": 4,
    "ytick.major.size": 4,
    "xtick.minor.size": 2,
    "ytick.minor.size": 2,
    "savefig.bbox": "tight",
    "savefig.pad_inches": 0.03,
})


def main():
    # Grid
    xmin, xmax, ymin, ymax = -2.0, 2.0, -2.0, 2.0
    n = 700
    x1 = np.linspace(xmin, xmax, n)
    x2 = np.linspace(ymin, ymax, n)
    X1, X2 = np.meshgrid(x1, x2)

    ZB = B(X1, X2)
    ZU = unsafe_fun(X1, X2)
    unsafe_mask = (ZU <= 0.0)

    # Trajectories (same initial conditions as ex4.py)
    initial_points = [
        (1.5, 0.5),
        (0.5, 0.5),
        (-1, -1),
    ]
    traj_colors = [
        "magenta",
        "cyan",
        "green",
    ]
    trajectories = [simulate(p, dt=0.01, T=50) for p in initial_points]

    # Figure
    fig, ax = plt.subplots(figsize=(7.0, 5.4), dpi=220)

    # Heatmap
    levels = np.linspace(float(np.min(ZB)), float(np.max(ZB)), 180)
    cf = ax.contourf(
        X1, X2, ZB,
        levels=levels,
        cmap="coolwarm_r",
        alpha=0.78,
        extend="both",
    )

    # Unsafe region overlay
    ax.contourf(
        X1, X2, unsafe_mask.astype(float),
        levels=[0.5, 1.5],
        colors=["#cc3d3d"],
        alpha=0.28,
    )

    # Unsafe boundary
    ax.contour(
        X1, X2, ZU,
        levels=[0.0],
        colors="#8b1e13",
        linewidths=1.4,
        linestyles="--",
    )

    # Barrier level set: B=0
    ax.contour(
        X1, X2, ZB,
        levels=[0.0],
        colors="blue",
        linewidths=1.8,
    )

    # Optional faint extra contours for barrier shape
    ax.contour(
        X1, X2, ZB,
        levels=[-10, -5, 5, 10],
        colors="white",
        linewidths=0.55,
        alpha=0.45,
    )

    # Plot trajectories + markers
    for traj, p, c in zip(trajectories, initial_points, traj_colors):
        ax.plot(traj[:, 0], traj[:, 1], color=c, lw=1.7, zorder=5)
        ax.scatter(
            [p[0]], [p[1]],
            s=12, color=c,
            edgecolors="black", linewidths=0.35,
            zorder=6
        )

    # Axes setup
    ax.set_xlim(xmin, xmax)
    ax.set_ylim(ymin, ymax)
    ax.set_aspect("equal", adjustable="box")
    ax.set_xlabel(r"$x_1$")
    ax.set_ylabel(r"$x_2$")
    ax.set_title(r"Explicit barrier level set $B(x_1,x_2)=0$", pad=6)

    ax.grid(True, linestyle=":", linewidth=0.45, alpha=0.5, color="k")
    ax.minorticks_on()

    # Legend (same style as ex3.py)
    legend_handles = [
        Line2D([0], [0], color="#8b1e13", lw=1.4, ls="--",
               label=r"Unsafe boundary $(x_1-0.7)^2+(x_2+0.7)^2=0.09$"),
        Line2D([0], [0], color="blue", lw=1.8,
               label=r"Barrier level set $B(x_1,x_2)=0$"),
    ]
    ax.legend(
        handles=legend_handles,
        loc="lower right",
        bbox_to_anchor=(0.98, 0.02),
        ncol=1,
        frameon=True,
        framealpha=0.95,
        fancybox=False,
        borderpad=0.45,
        columnspacing=1.0,
        handlelength=2.0,
    )

    # Colorbar
    cbar = fig.colorbar(cf, ax=ax, fraction=0.047, pad=0.03)
    cbar.set_label(r"Barrier value $B(x)$", rotation=90, fontsize=11)
    cbar.ax.tick_params(labelsize=9)

    # Save
    fig.savefig("ex4.3_barrier_heatmap.png", dpi=300)
    fig.savefig("ex4.3_barrier_heatmap.pdf")

    plt.close(fig)


if __name__ == "__main__":
    main()

