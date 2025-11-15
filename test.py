# smart_parking_revised.py
# Revisi oleh assistant — sesuai request user:
# - screen 1300x900
# - jalan putih = navigable nodes (parkir tidak dilalui)
# - entrance otomatis: y=1,2,3 -> north; y=4,5,6 -> south
# - save single-record JSON overwrite (option A)
# - popup + beep if all parking occupied
# - larger legend / panels to avoid text clipping

import pygame
import sys
import json
import math
import heapq
from collections import deque, defaultdict

# Optional beep via numpy if available (best effort)
try:
    import numpy as _np
    NUMPY_AVAILABLE = True
except Exception:
    NUMPY_AVAILABLE = False

pygame.init()
if NUMPY_AVAILABLE:
    pygame.mixer.init()

# --- CONFIG ---
SCREEN_WIDTH = 1200
SCREEN_HEIGHT = 800
FPS = 60

# Colors
WHITE = (255, 255, 255)
BLACK = (0, 0, 0)
BLUE = (100, 150, 255)
RED = (255, 100, 100)
GREEN = (100, 255, 100)
YELLOW = (255, 235, 130)
ORANGE = (255, 165, 0)
PINK = (255, 192, 203)
LIGHT_BLUE = (210, 230, 255)
GRAY = (200, 200, 200)
DARK_GRAY = (80, 80, 80)
NAVY = (10, 30, 80)
PURPLE = (170, 50, 170)
ALERT_RED = (200, 30, 30)

FONT_PATH = None  # default pygame font

# JSON file for saving single-record (overwrite)
JSON_PATH = "last_target_parking.json"

class SmartParkingSystem:
    def __init__(self):
        self.screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT))
        pygame.display.set_caption("Smart Parking System")
        self.clock = pygame.time.Clock()

        # Fonts (bigger sizes to avoid clipping)
        self.font_large = pygame.font.Font(FONT_PATH, 42)
        self.font_medium = pygame.font.Font(FONT_PATH, 28)
        self.font_small = pygame.font.Font(FONT_PATH, 20)
        self.font_tiny = pygame.font.Font(FONT_PATH, 16)

        self.state = "splash"  # splash or map
        self.animation_counter = 0

        # Layout parameters
        self.grid_size = 48
        self.grid_cols = 9
        self.grid_rows = 8

        # Offsets
        self.parking_offset_x = 40
        self.parking_offset_y = 120
        self.mall_offset_x = 560
        self.mall_offset_y = 120

        # Start / current position (purple marker)
        self.start_position = (1, 7)
        self.current_position = self.start_position

        # Data
        self.setup_shops()
        self.setup_parking_spots()
        # Build graph of navigable nodes (roads) - exclude parking spots
        self.build_graph()

        # Selection / path
        self.selected_shop = None
        self.algorithm = "A*"  # default
        self.path = []
        self.path_cost = 0
        self.target_parking = None

        # Occupied tracking
        self.occupied_parking = set()

        # UI interaction
        self.start_button_rect = None
        self.algo_buttons = {}
        self.popup_timer = 0

    def setup_shops(self):
        # define shops with positions (x,y). We'll compute entrance automatically based on y.
        # positions chosen to match mockup columns
        self.shops = {
            "SOGO": (1, 1),
            "Watsons": (4, 1),
            "Wing Stop": (7, 1),
            "Matahari": (1, 2),
            "Sephora": (4, 2),
            "Yoshinoya": (7, 2),
            "H&M": (1, 3),
            "This is April": (4, 3),
            "Hokben": (7, 3),
            "Miniso": (1, 4),
            "Gaudi": (4, 4),
            "Teazzi": (7, 4),
            "ZARA": (1, 5),
            "HMNS": (4, 5),
            "Sociolla": (7, 5),
            "Sour Sally": (1, 6),
            "Guardian": (4, 6),
            "Fore": (7, 6),
        }

    def setup_parking_spots(self):
        # parking coordinates (x,y). These are parking tiles (not traversable)
        self.initial_parking_spots = [
            (0,1),(0,2),(0,3),(0,4),(0,5),(0,6),
            (3,1),(3,2),(3,3),(3,4),(3,5),(3,6),
            (4,1),(4,2),(4,3),(4,4),(4,5),(4,6),
            (7,1),(7,2),(7,3),(7,4),(7,5),(7,6)
        ]
        self.parking_spots = list(self.initial_parking_spots)

    def build_graph(self):
        """Build adjacency list for navigable nodes (exclude parking spots).
        Nodes are grid coordinates (x,y). Roads include all nodes except those in parking_spots.
        """
        self.graph = defaultdict(list)
        self.positions = {}

        for x in range(self.grid_cols):
            for y in range(self.grid_rows):
                # store pixel center for drawing
                center_x = self.parking_offset_x + x * self.grid_size + self.grid_size // 2
                center_y = self.parking_offset_y + y * self.grid_size + self.grid_size // 2
                self.positions[(x, y)] = (center_x, center_y)

        # navigable nodes = all nodes that are NOT parking_spots
        self.navigable = set((x,y) for x in range(self.grid_cols) for y in range(self.grid_rows)
                             if (x,y) not in self.parking_spots)

        # ensure start position is navigable (if it's a parking spot we allow it)
        if self.start_position not in self.navigable:
            self.navigable.add(self.start_position)

        # Build adjacency for navigable nodes
        deltas = [(0,1),(1,0),(0,-1),(-1,0)]
        for node in list(self.navigable):
            x,y = node
            for dx,dy in deltas:
                nx,ny = x+dx, y+dy
                if 0 <= nx < self.grid_cols and 0 <= ny < self.grid_rows:
                    # neighbor must be navigable OR might be target (handled in search)
                    if (nx,ny) in self.navigable:
                        self.graph[node].append(((nx,ny), 1))

        # Note: parking nodes are intentionally NOT in graph; when computing path to a parking,
        # we'll allow an end node by connecting it temporally to adjacent navigable nodes.

    def get_entrance_position(self, shop_name):
        """Compute entrance coordinate (parking grid) based on shop y value.
        Shops with y in 1,2,3 -> north (entrance at row 0)
        Shops with y in 4,5,6 -> south (entrance at row grid_rows-1)
        Entrance x aligned with shop x (or nearest valid)
        """
        if shop_name not in self.shops:
            return (1, 0)
        x,y = self.shops[shop_name]
        if y in (1,2,3):
            entrance_y = 0
        else:
            entrance_y = self.grid_rows - 1
        # clamp x to grid
        ex = max(0, min(self.grid_cols-1, x))
        return (ex, entrance_y)

    # ---------------- Pathfinding algorithms ----------------
    def heuristic(self, a, b):
        return abs(a[0]-b[0]) + abs(a[1]-b[1])

    def neighbors_for_search(self, current, end):
        """Return list of neighbors for current during search.
        We treat neighbors that are navigable normally. We also allow the 'end' node
        even if it's a parking spot by connecting end to its adjacent navigable nodes.
        """
        results = []
        # standard neighbors from self.graph if current is navigable
        if current in self.graph:
            for nb, cost in self.graph[current]:
                results.append((nb, cost))

        # if current is adjacent to the end (end may be parking), add end as neighbor
        if end is not None:
            ex,ey = end
            cx,cy = current
            if abs(ex-cx) + abs(ey-cy) == 1:
                # allow stepping into the end even if it's a parking spot (cost 1)
                results.append((end, 1))

        return results

    def bfs(self, start, end):
        queue = deque([(start, [start])])
        visited = {start}
        while queue:
            current, path = queue.popleft()
            if current == end:
                return path, len(path)-1
            for neighbor, _ in self.neighbors_for_search(current, end):
                if neighbor not in visited:
                    visited.add(neighbor)
                    queue.append((neighbor, path + [neighbor]))
        return [], 0

    def dfs(self, start, end):
        stack = [(start, [start])]
        visited = {start}
        while stack:
            current, path = stack.pop()
            if current == end:
                return path, len(path)-1
            for neighbor, _ in self.neighbors_for_search(current, end):
                if neighbor not in visited:
                    visited.add(neighbor)
                    stack.append((neighbor, path + [neighbor]))
        return [], 0

    def gbfs(self, start, end):
        """Greedy Best First Search"""
        open_set = []
        heapq.heappush(open_set, (self.heuristic(start, end), start))
        came_from = {}
        visited = set([start])

        while open_set:
            _, current = heapq.heappop(open_set)

            if current == end:
                # reconstruct
                path = [current]
                while current in came_from:
                    current = came_from[current]
                    path.append(current)
                path.reverse()
                return path, len(path) - 1

            for neighbor, _ in self.neighbors_for_search(current, end):
                if neighbor not in visited:
                    visited.add(neighbor)
                    came_from[neighbor] = current
                    h = self.heuristic(neighbor, end)
                    heapq.heappush(open_set, (h, neighbor))

        return [], 0

    def a_star(self, start, end):
        open_heap = []
        heapq.heappush(open_heap, (0 + self.heuristic(start, end), 0, start))
        came_from = {}
        gscore = {start: 0}
        closed = set()
        while open_heap:
            f, g, current = heapq.heappop(open_heap)
            if current == end:
                # reconstruct
                path = [current]
                while current in came_from:
                    current = came_from[current]
                    path.append(current)
                path.reverse()
                return path, len(path)-1
            if current in closed:
                continue
            closed.add(current)
            for neighbor, cost in self.neighbors_for_search(current, end):
                tentative_g = g + cost
                if tentative_g < gscore.get(neighbor, 1e9):
                    came_from[neighbor] = current
                    gscore[neighbor] = tentative_g
                    fscore = tentative_g + self.heuristic(neighbor, end)
                    heapq.heappush(open_heap, (fscore, tentative_g, neighbor))
        return [], 0

    def find_closest_parking(self, entrance_pos):
        best = None
        best_dist = float('inf')
        for spot in self.parking_spots:
            if spot in self.occupied_parking:
                continue
            # compute Manhattan distance from entrance to parking spot
            d = abs(spot[0] - entrance_pos[0]) + abs(spot[1] - entrance_pos[1])
            if d < best_dist:
                best_dist = d
                best = spot
        return best

    def find_path(self, shop_name, algorithm):
        if shop_name not in self.shops:
            return
        # compute entrance by y rule
        entrance = self.get_entrance_position(shop_name)
        parking = self.find_closest_parking(entrance)
        if parking is None:
            # no parking available
            self.path = []
            self.target_parking = None
            self.selected_shop = shop_name
            return

        self.target_parking = parking
        self.selected_shop = shop_name
        self.algorithm = algorithm

        start = self.current_position
        end = parking

        if algorithm == "BFS":
            path, cost = self.bfs(start, end)
        elif algorithm == "DFS":
            path, cost = self.dfs(start, end)
        elif algorithm == "GBFS":
            path, cost = self.gbfs(start, end)
        else:
            path, cost = self.a_star(start, end)

        # path might be empty (no path found)
        self.path = path
        self.path_cost = cost

    def mark_parking_occupied(self):
        if self.target_parking:
            self.occupied_parking.add(self.target_parking)
            # update current position to that parking
            self.current_position = self.target_parking
            # save JSON (overwrite single-record)
            self.save_target_json()
            # clear path after marking
            self.path = []
            self.target_parking = None
            # if all full, trigger popup + beep
            if len(self.occupied_parking) >= len(self.parking_spots):
                self.trigger_full_popup()

    def save_target_json(self):
        rec = {
            "shop": self.selected_shop,
            "parking": list(self.current_position),
            "algorithm": self.algorithm,
            "path": [list(node) for node in self.path]  # current path (probably cleared)
        }
        try:
            with open(JSON_PATH, "w") as f:
                json.dump(rec, f, indent=2)
        except Exception as e:
            print("Error saving JSON:", e)

    def trigger_full_popup(self):
        # set popup state (we'll draw it in draw_map)
        self.popup_timer = 180  # 3 seconds @ 60fps
        # try beep
        self.try_beep()

    def try_beep(self):
        # Try numpy generated tone if available
        if NUMPY_AVAILABLE:
            try:
                freq = 880
                duration = 0.25
                sample_rate = 44100
                t = _np.linspace(0, duration, int(sample_rate * duration), False)
                tone = _np.sin(freq * 2 * _np.pi * t) * 0.5
                # convert to 16-bit signed ints
                audio = _np.int16(tone * 32767)
                sound = pygame.sndarray.make_sound(audio)
                sound.play()
            except Exception:
                try:
                    print('\a', end='', flush=True)
                except Exception:
                    pass
        else:
            try:
                print('\a', end='', flush=True)
            except Exception:
                pass

    # ---------------- Drawing functions ----------------
    def draw_splash(self):
        self.screen.fill(WHITE)
        
        # Title
        title = self.font_large.render("Smart Parking System", True, BLACK)
        self.screen.blit(title, (SCREEN_WIDTH // 2 - title.get_width() // 2, 200))
        
        # Creators
        creators_y = 320
        creators = [
            "create by:",
            "• Salwa Nadia Maharani",
            "• Naura Rossa Azalia",
            "• Kinanti Ayu Caesandria"
        ]
        
        for i, creator in enumerate(creators):
            text = self.font_small.render(creator, True, BLACK)
            self.screen.blit(text, (SCREEN_WIDTH // 2 - text.get_width() // 2, creators_y + i * 50))
        
        # Continue text with blinking effect
        if (self.animation_counter // 30) % 2 == 0:
            continue_text = self.font_small.render("press any key or click to continue...", True, DARK_GRAY)
            self.screen.blit(continue_text, (SCREEN_WIDTH // 2 - continue_text.get_width() // 2, 650))
        
        self.animation_counter += 1

    def draw_parking_layout(self):
        # Title
        title = self.font_medium.render("Layout Parkiran", True, BLACK)
        self.screen.blit(title, (self.parking_offset_x, self.parking_offset_y - 40))

        # grid (light)
        for x in range(self.grid_cols):
            for y in range(self.grid_rows):
                rx = self.parking_offset_x + x*self.grid_size
                ry = self.parking_offset_y + y*self.grid_size
                pygame.draw.rect(self.screen, LIGHT_BLUE, (rx, ry, self.grid_size, self.grid_size), 1)

        # draw parking spots (filled squares)
        for spot in self.parking_spots:
            sx, sy = spot
            rx = self.parking_offset_x + sx*self.grid_size
            ry = self.parking_offset_y + sy*self.grid_size
            color = RED if spot in self.occupied_parking else BLUE
            pygame.draw.rect(self.screen, color, (rx+4, ry+4, self.grid_size-8, self.grid_size-8))
            pygame.draw.rect(self.screen, BLACK, (rx+4, ry+4, self.grid_size-8, self.grid_size-8), 2)

        # draw entrances (green small squares) - north and south indicators
        # North at row 0 (x positions to indicate entries)
        north_positions = [(0,0)]
        south_positions = [(0,self.grid_rows-1)]
        for ex,ey in north_positions+south_positions:
            cx,cy = self.positions.get((ex,ey),(0,0))
            pygame.draw.rect(self.screen, GREEN, (cx-6, cy-6, 12, 12))
            pygame.draw.rect(self.screen, BLACK, (cx-6, cy-6, 12, 12), 1)

        # Draw path (navy dots) - path may include end parking node, which is not navigable normally
        if self.path and len(self.path) > 0:
            for i,node in enumerate(self.path):
                px,py = self.positions[node]
                # avoid drawing dot inside parking tile (draw at center)
                pygame.draw.circle(self.screen, NAVY, (int(px), int(py)), 6)
                # draw small steps/dots between nodes optionally
                #if i < len(self.path)-1:
                #    nx,ny = self.positions[self.path[i+1]]
                #    pygame.draw.line(self.screen, NAVY, (px,py), (nx,ny), 3)

        # draw target parking blinking
        if self.target_parking:
            tx,ty = self.target_parking
            rx = self.parking_offset_x + tx*self.grid_size
            ry = self.parking_offset_y + ty*self.grid_size
            if (self.animation_counter // 20) % 2 == 0:
                pygame.draw.rect(self.screen, PINK, (rx+6, ry+6, self.grid_size-12, self.grid_size-12))
            pygame.draw.rect(self.screen, BLACK, (rx+6, ry+6, self.grid_size-12, self.grid_size-12), 2)

        # draw current position (purple circle)
        if self.current_position in self.positions:
            cx,cy = self.positions[self.current_position]
            pygame.draw.circle(self.screen, PURPLE, (int(cx), int(cy)), 14)
            pygame.draw.circle(self.screen, BLACK, (int(cx), int(cy)), 14, 2)

    def draw_mall_layout(self):
        # title
        title = self.font_medium.render("Layout Mall", True, BLACK)
        self.screen.blit(title, (self.mall_offset_x, self.mall_offset_y - 40))

        # mall grid
        cols = 9
        rows = 8
        for x in range(cols):
            for y in range(rows):
                rx = self.mall_offset_x + x*self.grid_size
                ry = self.mall_offset_y + y*self.grid_size
                pygame.draw.rect(self.screen, LIGHT_BLUE, (rx, ry, self.grid_size, self.grid_size), 1)

        # draw shops
        for shop_name, (sx,sy) in self.shops.items():
            rx = self.mall_offset_x + sx*self.grid_size
            ry = self.mall_offset_y + sy*self.grid_size
            rect = pygame.Rect(rx+2, ry+2, self.grid_size-4, self.grid_size-4)
            color = ORANGE if shop_name == self.selected_shop else YELLOW
            pygame.draw.rect(self.screen, color, rect)
            pygame.draw.rect(self.screen, BLACK, rect, 2)
            # text wrap: try to fit name in two lines
            words = shop_name.split()
            line1 = words[0] if len(words) > 0 else ""
            line2 = " ".join(words[1:]) if len(words) > 1 else ""
            t1 = self.font_tiny.render(line1, True, BLACK)
            self.screen.blit(t1, (rx+6, ry+5))
            if line2:
                t2 = self.font_tiny.render(line2, True, BLACK)
                self.screen.blit(t2, (rx+6, ry+5+16))

    def draw_legend(self):
        legend_x = 30
        legend_y = SCREEN_HEIGHT - 250
        w = 360
        h = 170

        pygame.draw.rect(self.screen, LIGHT_BLUE, (legend_x, legend_y, w, h))
        pygame.draw.rect(self.screen, BLACK, (legend_x, legend_y, w, h), 2)

        title = self.font_small.render("Keterangan Warna:", True, BLACK)
        self.screen.blit(title, (legend_x + 12, legend_y + 8))

        items_left = [
            ("Posisi sekarang", PURPLE),
            ("Parkir kosong", BLUE),
            ("Parkir terisi", RED),
            ("Pintu masuk mall", GREEN),
        ]

        items_right = [
            ("Toko", YELLOW),
            ("Toko tujuan", ORANGE),
            ("Jalur yang disarankan", NAVY),
            ("Target parkir", PINK)
        ]

        # posisi kolom kiri
        x_left = legend_x + 12
        y_start = legend_y + 40

        # posisi kolom kanan
        x_right = legend_x + 190   # geser ke kanan
        y_right = legend_y + 40

        # Gambar kolom kiri
        y = y_start
        for label, color in items_left:
            pygame.draw.rect(self.screen, color, (x_left, y, 20, 20))
            pygame.draw.rect(self.screen, BLACK, (x_left, y, 20, 20), 1)

            text = self.font_tiny.render(label, True, BLACK)
            self.screen.blit(text, (x_left + 30, y + 2))

            y += 28

        # Gambar kolom kanan
        y = y_right
        for label, color in items_right:
            pygame.draw.rect(self.screen, color, (x_right, y, 20, 20))
            pygame.draw.rect(self.screen, BLACK, (x_right, y, 20, 20), 1)

            text = self.font_tiny.render(label, True, BLACK)
            self.screen.blit(text, (x_right + 30, y + 2))

            y += 28

    def draw_control_panel(self):
        px = 420
        py = SCREEN_HEIGHT - 250
        w = 400
        h = 170
        pygame.draw.rect(self.screen, LIGHT_BLUE, (px, py, w, h))
        pygame.draw.rect(self.screen, BLACK, (px, py, w, h), 2)
        title = self.font_small.render("Pilihan Metode:", True, BLACK)
        self.screen.blit(title, (px+12, py+8))

        algos = ["DFS","BFS","GBFS","A*"]
        # spread buttons
        gap = 90
        start_x = px + 18
        self.algo_buttons.clear()
        for i,algo in enumerate(algos):
            bx = start_x + i*gap
            rect = pygame.Rect(bx, py+40, 80, 36)
            color = GREEN if self.algorithm == algo else GRAY
            pygame.draw.rect(self.screen, color, rect)
            pygame.draw.rect(self.screen, BLACK, rect, 2)
            t = self.font_small.render(algo, True, BLACK)
            tr = t.get_rect(center=rect.center)
            self.screen.blit(t, tr)
            self.algo_buttons[algo] = rect

        # START button
        sr = pygame.Rect(px+110, py+92, 220, 56)
        self.start_button_rect = sr
        pygame.draw.rect(self.screen, (160,255,160), sr)
        pygame.draw.rect(self.screen, BLACK, sr, 3)
        st = self.font_medium.render("START", True, BLACK)
        self.screen.blit(st, st.get_rect(center=sr.center))

    def draw_info_panel(self):
        ix = SCREEN_WIDTH - 360
        iy = SCREEN_HEIGHT - 250
        w = 340
        h = 170
        pygame.draw.rect(self.screen, LIGHT_BLUE, (ix, iy, w, h))
        pygame.draw.rect(self.screen, BLACK, (ix, iy, w, h), 2)
        title = self.font_small.render("Detail Informasi:", True, BLACK)
        self.screen.blit(title, (ix+12, iy+8))

        if self.selected_shop:
            lines = [
                f"Shop: {self.selected_shop}",
                f"Algorithm: {self.algorithm}",
                f"Path length (nodes): {len(self.path)}",
                f"Cost (steps): {int(self.path_cost)}",
                f"Target parking: {str(self.target_parking) if self.target_parking else '-'}"
            ]
            y = iy+36
            for line in lines:
                txt = self.font_tiny.render(line, True, BLACK)
                self.screen.blit(txt, (ix+12, y))
                y += 26
        else:
            txt = self.font_tiny.render("Pilih toko terlebih dahulu", True, DARK_GRAY)
            self.screen.blit(txt, (ix+12, iy+50))

    def draw_popup_full(self):
        # centered red popup with warning text
        w = 600
        h = 180
        x = SCREEN_WIDTH//2 - w//2
        y = SCREEN_HEIGHT//2 - h//2
        pygame.draw.rect(self.screen, ALERT_RED, (x,y,w,h))
        pygame.draw.rect(self.screen, BLACK, (x,y,w,h), 4)
        title = self.font_large.render("SEMUA PARKIRAN PENUH!", True, WHITE)
        subtitle = self.font_medium.render("Mohon maaf, tidak ada slot tersisa.", True, WHITE)
        self.screen.blit(title, (x + w//2 - title.get_width()//2, y+30))
        self.screen.blit(subtitle, (x + w//2 - subtitle.get_width()//2, y+100))

    def handle_click(self, pos):
        # Check mall shop click
        for shop_name, (sx,sy) in self.shops.items():
            rx = self.mall_offset_x + sx*self.grid_size + 2
            ry = self.mall_offset_y + sy*self.grid_size + 2
            rect = pygame.Rect(rx, ry, self.grid_size-4, self.grid_size-4)
            if rect.collidepoint(pos):
                # select shop and compute path
                self.find_path(shop_name, self.algorithm)
                return

        # algorithm buttons
        for algo, rect in self.algo_buttons.items():
            if rect.collidepoint(pos):
                self.algorithm = algo
                if self.selected_shop:
                    self.find_path(self.selected_shop, self.algorithm)
                return

        # START button
        if self.start_button_rect and self.start_button_rect.collidepoint(pos):
            # require selected shop and target_parking (found earlier when selecting shop)
            if self.selected_shop and self.target_parking:
                self.mark_parking_occupied()
            else:
                # nothing selected; small feedback (blink)
                pass

    def handle_event(self, event):
        if event.type == pygame.QUIT:
            return False
        if event.type == pygame.KEYDOWN:
            if self.state == "splash":
                self.state = "map"
            else:
                # keyboard shortcuts: space to open splash? ignore
                pass
        if event.type == pygame.MOUSEBUTTONDOWN:
            if self.state == "splash":
                self.state = "map"
            else:
                self.handle_click(event.pos)
        return True

    def run(self):
        running = True
        while running:
            for event in pygame.event.get():
                running = self.handle_event(event)

            self.screen.fill(WHITE)
            if self.state == "splash":
                self.draw_splash()
            else:
                # draw map and UI
                self.draw_parking_layout()
                self.draw_mall_layout()
                self.draw_legend()
                self.draw_control_panel()
                self.draw_info_panel()
                # popup if triggered
                if self.popup_timer > 0:
                    self.draw_popup_full()
                    self.popup_timer -= 1

            pygame.display.flip()
            self.clock.tick(FPS)
            self.animation_counter += 1

        pygame.quit()
        sys.exit()

if __name__ == "__main__":
    app = SmartParkingSystem()
    app.run()
