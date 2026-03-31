# 这个代码只是显示这个动力学

import numpy as np
import matplotlib.pyplot as plt
from scipy.integrate import solve_ivp

# 1. 定义状态空间网格
x1_min, x1_max = -2.0, 2.0
x2_min, x2_max = -2.0, 2.0
X1, X2 = np.meshgrid(np.linspace(x1_min, x1_max, 400),
                     np.linspace(x2_min, x2_max, 400))

# 2. 定义系统无控制动力学
def system_dynamics(t, state):
    x1, x2 = state
    dx1 = np.exp(-x1) + x2 - 1
    dx2 = -(np.sin(x1))**2
    return [dx1, dx2]

# 计算向量场用于绘制流线图
U = np.exp(-X1) + X2 - 1
V = -(np.sin(X1))**2

# 3. 定义几何不安全区域 (小圆)
unsafe_condition = (X1 - 0.7)**2 + (X2 + 0.7)**2 - 0.09

fig, ax = plt.subplots(figsize=(10, 8))

# 绘制向量场流线 (核心动力学真相)
# 流线密度设为 1.5，颜色用流速着色
speed = np.sqrt(U**2 + V**2)
strm = ax.streamplot(X1, X2, U, V, color=speed, cmap='viridis', linewidth=1.5, density=1.5, arrowsize=1.5)
fig.colorbar(strm.lines, ax=ax, label='Vector Field Speed')

# 绘制几何不安全区域 (红色实心圆)
ax.contourf(X1, X2, unsafe_condition, levels=[-np.inf, 0], colors=['red'], alpha=0.6)
ax.contour(X1, X2, unsafe_condition, levels=[0], colors='darkred', linewidths=2, linestyles='--')

# 标注我们刚才验证的“撞击点”
ax.plot(0.7, -0.4, marker='*', color='yellow', markersize=15, markeredgecolor='black', label='Critical Point $\dot{\mathcal{B}}_{geom} < 0$')

# --- 仿真几条极限边缘轨迹 ---
initial_conditions = [
    (1.5, 0.5),    # 从右上角出发，观察如何被吸引
    (0.8, -0.2),    # 极其危险的点，几乎贴着圆上方出发
    (-1.5,1.5)
]

t_span = (0, 100)
t_eval = np.linspace(t_span[0], t_span[1], 1000)
traj_colors = ['magenta', 'cyan','blue']

for ic, color in zip(initial_conditions, traj_colors):
    sol = solve_ivp(system_dynamics, t_span, ic, t_eval=t_eval, method='RK45')
    ax.plot(sol.y[0], sol.y[1], color=color, linewidth=2.5, label=f'Trajectory from {ic}')
    ax.plot(ic[0], ic[1], marker='o', markeredgecolor='black', color=color, markersize=8)

ax.set_xlim([x1_min, x1_max])
ax.set_ylim([x2_min, x2_max])
ax.set_xlabel('$x_1$', fontsize=12)
ax.set_ylabel('$x_2$', fontsize=12)
ax.set_title('Transcendental System: Vector Field & Inherent Danger', fontsize=14)
ax.legend(loc='upper right')
plt.grid(True, linestyle=':', alpha=0.5, color='black')
plt.show()