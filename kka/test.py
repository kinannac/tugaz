import pygame
import sys
import json
import math
import heapq
from collections import deque, defaultdict

pygame.init() 

# Mengatur ukuran layar aplikasi dan frame per second animasi 
SCREEN_WIDTH = 1200
SCREEN_HEIGHT = 800
FPS = 50

# Warna yang dipakai untuk menggambarkan objek di layar 
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

class SmartParkingSystem:
    def __init__(self):
        # setup pygame 
        self.screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT)) # ukuran layar 
        pygame.display.set_caption("Smart Parking System") # judul aplikasi 
        self.clock = pygame.time.Clock() # pengatur frame rate

        # Inisialisasi Font 
        self.font_xl = pygame.font.SysFont("Times New Roman", 42) 
        self.font_l = pygame.font.SysFont("Times New Roman", 28)
        self.font_m = pygame.font.SysFont("Times New Roman", 24)
        self.font_s = pygame.font.SysFont("Times New Roman", 20)
        self.font_xs = pygame.font.SysFont("Times New Roman", 16)
        self.state = "splash" # state awal aplikasi 
        self.animation_counter = 0 # counter untuk animasi 

        # Grid dan layout 
        self.grid_size = 48 
        self.grid_cols = 9
        self.grid_rows = 8

        # Offsets untuk menggambar layout parkiran dan mall 
        self.parking_offset_x = 40 
        self.parking_offset_y = 120
        self.mall_offset_x = 560
        self.mall_offset_y = 120

        # Start node
        self.start_position = (1, 7) # posisi awal mobil 
        self.current_position = self.start_position # posisi mobil saat ini 

        # Setup shops dan parking spots
        self.setup_shops() # daftar toko di mall
        self.setup_parking_spots() # daftar sopot parkir 
        self.build_graph() # graf jalur parkir 
        self.cars_entered = 0  # jumlah mobil yang sudah masuk parkiran

        # Pathfinding state 
        self.selected_shop = None 
        self.algorithm = "A*"  
        self.path = [] 
        self.path_cost = 0
        self.target_parking = None

        # Parking occupancy
        self.occupied_parking = set()

        # UI interaction
        self.start_button_rect = None
        self.algo_buttons = {}
        self.popup_timer = 0

        self.moving = False 
        self.movement_queue = []
        self.movement_speed = 12   # frame per step
        self.movement_counter = 0

        self.load_parking_data()

    # Setup shops and parking spots
    def setup_shops(self):
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

    # Setup parking spots
    def setup_parking_spots(self): 
        self.initial_parking_spots = [
            (0,1),(0,2),(0,3),(0,4),(0,5),(0,6), 
            (3,1),(3,2),(3,3),(3,4),(3,5),(3,6), 
            (4,1),(4,2),(4,3),(4,4),(4,5),(4,6),
            (7,1),(7,2),(7,3),(7,4),(7,5),(7,6)
        ]
        self.parking_spots = list(self.initial_parking_spots)
        
    # Build graph for pathfinding
    def build_graph(self): # membuat graf jalur parkir
        self.graph = defaultdict(list) 
        self.positions = {}

        for x in range(self.grid_cols): # kolom grid
            for y in range(self.grid_rows): # baris grid
                # hitung posisi tengah setiap node
                center_x = self.parking_offset_x + x * self.grid_size + self.grid_size // 2 # posisi x tengah
                center_y = self.parking_offset_y + y * self.grid_size + self.grid_size // 2 # posisi y tengah
                self.positions[(x, y)] = (center_x, center_y) # simpan posisi tengah node

        # navigable nodes = semua node kecuali parkiran
        self.navigable = set((x,y) for x in range(self.grid_cols) for y in range(self.grid_rows) # 
                             if (x,y) not in self.parking_spots) 
        if self.start_position not in self.navigable:
            self.navigable.add(self.start_position)

        # buat edges antar node
        deltas = [(0,1),(1,0),(0,-1),(-1,0)] # arah gerak: bawah, kanan, atas, kiri
        for node in list(self.navigable): # setiap node yang bisa dilalui
            x,y = node 
            for dx,dy in deltas: 
                nx,ny = x+dx, y+dy
                if 0 <= nx < self.grid_cols and 0 <= ny < self.grid_rows:
                    if (nx,ny) in self.navigable:
                        self.graph[node].append(((nx,ny), 1))
    
    # Tentukan posisi pintu masuk berdasarkan toko
    def get_entrance_position(self, shop_name):
        if shop_name not in self.shops:
            return (0, 0)   # default fallback

        x, y = self.shops[shop_name]

        # toko di bagian utara (y = 1,2,3)
        if y <= 3:
            return (0, 0)   # pintu utara

        # toko di bagian selatan (y = 4,5,6)
        return (0, self.grid_rows - 1)  # pintu selatan (0,7)

    # Heuristic function for A* and GBFS
    def heuristic(self, a, b):
        return abs(a[0]-b[0]) + abs(a[1]-b[1])

    # Get neighbors for pathfinding
    def neighbors_for_search(self, node, goal):
        x, y = node
        dirs = [(1,0), (-1,0), (0,1), (0,-1)]
        result = []

        # cek semua arah
        for dx, dy in dirs:
            nx, ny = x + dx, y + dy
            # batas grid
            if nx < 0 or nx >= self.grid_cols or ny < 0 or ny >= self.grid_rows:
                continue
            # tidak boleh lewat pintu
            if node != (0, 0) and (nx, ny) in [(0, 0), (0, self.grid_rows - 1)]:
                continue
            # tidak boleh lewat parkiran
            if (nx, ny) in self.occupied_parking and (nx, ny) != goal:
                continue
            if (nx, ny) in self.parking_spots and (nx, ny) != goal:
                continue
            # tambahkan neighbor
            result.append(((nx, ny), 1))

        return result

    # BFS implementation
    def bfs(self, start, end):
        queue = deque([(start, [start])])
        visited = {start}
        # BFS loop
        while queue:
            current, path = queue.popleft()
            # check goal
            if current == end:
                return path, len(path)-1
            # explore neighbors
            for neighbor, _ in self.neighbors_for_search(current, end):
                if neighbor not in visited:
                    visited.add(neighbor)
                    queue.append((neighbor, path + [neighbor]))
        return [], 0
    
    # DFS implementation
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

    # GBFS implementation
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
    
    # A* implementation
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

    def find_closest_parking_with_pathfinding(self, entrance):
        best = None
        best_cost = float('inf')

        for spot in self.parking_spots:
            if spot in self.occupied_parking:
                continue

            path, cost = self.a_star(entrance, spot)

            if path and cost < best_cost:
                best_cost = cost
                best = spot

        return best

    def find_path(self, shop_name, algorithm):

        # tentukan pintu mall
        entrance = self.get_entrance_position(shop_name)

        # pilih parkiran terdekat dari pintu mall
        parking = self.find_closest_parking_with_pathfinding(entrance)

        if parking is None:
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

        self.path = path
        self.path_cost = cost

    def mark_parking_occupied(self):
        if self.target_parking and self.path:
            self.movement_queue = self.path[1:].copy()
            self.moving = True
            self.movement_counter = 0

            # trigger popup jika penuh
            if len(self.occupied_parking) >= len(self.parking_spots):
                self.trigger_full_popup()
    
    def animate_movement(self):
        """Animates the car moving step-by-step along the path"""
        if not self.moving or not self.movement_queue:
            return

        self.movement_counter += 1

        if self.movement_counter >= self.movement_speed:
            self.movement_counter = 0
            
            # ambil node berikutnya
            next_pos = self.movement_queue.pop(0)
            self.current_position = next_pos

            # jika sudah sampai target parking
            if not self.movement_queue:
                self.moving = False

                # setelah sampai → tandai parkir sebagai occupied
                self.occupied_parking.add(self.current_position)

                # save JSON
                self.cars_entered += 1
                self.save_parking_data()

                # hapus path dari layar
                self.path = []
                self.target_parking = None

                # tampilkan popup jika penuh
                if len(self.occupied_parking) >= len(self.parking_spots):
                    self.trigger_full_popup()

    def save_parking_data(self):
        data = {
            "occupied": [list(pos) for pos in self.occupied_parking],
            "cars_entered": self.cars_entered
        }

        try:
            with open("parking_data.json", "w") as f:
                json.dump(data, f, indent=4)
        except:
            print("Error saving JSON")


    def trigger_full_popup(self):
        self.popup_timer = 180 
        self.try_beep()

    # fungsi draw
    def draw_splash(self):
        self.screen.fill(WHITE)
        
        # judul
        title = self.font_xl.render("Smart Parking System", True, BLACK)
        self.screen.blit(title, (SCREEN_WIDTH // 2 - title.get_width() // 2, 200))
        
        # creators
        creators_y = 320
        creators = [
            "create by:",
            "Salwa Nadia Maharani",
            "Naura Rossa Azalia",
            "Kinanti Ayu Caesandria"
        ]
        
        for i, creator in enumerate(creators):
            text = self.font_m.render(creator, True, BLACK)
            self.screen.blit(text, (SCREEN_WIDTH // 2 - text.get_width() // 2, creators_y + i * 50))
        
        # continue (efek blink)
        if (self.animation_counter // 30) % 2 == 0:
            continue_text = self.font_m.render("press any key or click to continue...", True, DARK_GRAY)
            self.screen.blit(continue_text, (SCREEN_WIDTH // 2 - continue_text.get_width() // 2, 650))
        
        self.animation_counter += 1

    def draw_parking_layout(self):
        # judul
        title = self.font_l.render("Layout Parkiran", True, BLACK)
        self.screen.blit(title, (self.parking_offset_x, self.parking_offset_y - 40))

        # grid layout
        for x in range(self.grid_cols):
            for y in range(self.grid_rows):
                rx = self.parking_offset_x + x*self.grid_size
                ry = self.parking_offset_y + y*self.grid_size
                pygame.draw.rect(self.screen, LIGHT_BLUE, (rx, ry, self.grid_size, self.grid_size), 1)

        # parking spots
        for spot in self.parking_spots:
            sx, sy = spot
            rx = self.parking_offset_x + sx*self.grid_size
            ry = self.parking_offset_y + sy*self.grid_size
            color = RED if spot in self.occupied_parking else BLUE
            pygame.draw.rect(self.screen, color, (rx+4, ry+4, self.grid_size-8, self.grid_size-8))
            pygame.draw.rect(self.screen, BLACK, (rx+4, ry+4, self.grid_size-8, self.grid_size-8), 2)

        # pintu masuk mall
        north_positions = [(0,0)]
        south_positions = [(0,self.grid_rows-1)]
        for ex,ey in north_positions+south_positions:
            cx,cy = self.positions.get((ex,ey),(0,0))
            pygame.draw.rect(self.screen, GREEN, (cx-6, cy-6, 12, 12))
            pygame.draw.rect(self.screen, BLACK, (cx-6, cy-6, 12, 12), 1)

        if self.path and len(self.path) > 0:
            for i,node in enumerate(self.path):
                px,py = self.positions[node]
                pygame.draw.circle(self.screen, NAVY, (int(px), int(py)), 6)
        
        # parkiran target blink
        if self.target_parking:
            tx,ty = self.target_parking
            rx = self.parking_offset_x + tx*self.grid_size
            ry = self.parking_offset_y + ty*self.grid_size
            if (self.animation_counter // 20) % 2 == 0:
                pygame.draw.rect(self.screen, PINK, (rx+6, ry+6, self.grid_size-12, self.grid_size-12))
            pygame.draw.rect(self.screen, BLACK, (rx+6, ry+6, self.grid_size-12, self.grid_size-12), 2)

        # posisi sekarang 
        if self.current_position in self.positions:
            cx,cy = self.positions[self.current_position]
            pygame.draw.circle(self.screen, PURPLE, (int(cx), int(cy)), 14)
            pygame.draw.circle(self.screen, BLACK, (int(cx), int(cy)), 14, 2)

    def draw_mall_layout(self):
        # judul
        title = self.font_l.render("Layout Mall", True, BLACK)
        self.screen.blit(title, (self.mall_offset_x, self.mall_offset_y - 40))

        # mall grid
        cols = 9
        rows = 8
        for x in range(cols):
            for y in range(rows):
                rx = self.mall_offset_x + x*self.grid_size
                ry = self.mall_offset_y + y*self.grid_size
                pygame.draw.rect(self.screen, LIGHT_BLUE, (rx, ry, self.grid_size, self.grid_size), 1)

        # pertokoan
        for shop_name, (sx,sy) in self.shops.items():
            rx = self.mall_offset_x + sx*self.grid_size
            ry = self.mall_offset_y + sy*self.grid_size
            rect = pygame.Rect(rx+2, ry+2, self.grid_size-4, self.grid_size-4)
            color = ORANGE if shop_name == self.selected_shop else YELLOW
            pygame.draw.rect(self.screen, color, rect)
            pygame.draw.rect(self.screen, BLACK, rect, 2)
            words = shop_name.split()
            line1 = words[0] if len(words) > 0 else ""
            line2 = " ".join(words[1:]) if len(words) > 1 else ""
            t1 = self.font_xs.render(line1, True, BLACK)
            self.screen.blit(t1, (rx+6, ry+5))
            if line2:
                t2 = self.font_xs.render(line2, True, BLACK)
                self.screen.blit(t2, (rx+6, ry+5+16))

    def draw_legend(self):
        legend_x = 30
        legend_y = SCREEN_HEIGHT - 250
        w = 370
        h = 170

        pygame.draw.rect(self.screen, LIGHT_BLUE, (legend_x, legend_y, w, h))
        pygame.draw.rect(self.screen, BLACK, (legend_x, legend_y, w, h), 2)

        title = self.font_s.render("Keterangan Warna:", True, BLACK)
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
        x_right = legend_x + 190
        y_right = legend_y + 40

        # buat kolom kiri
        y = y_start
        for label, color in items_left:
            pygame.draw.rect(self.screen, color, (x_left, y, 20, 20))
            pygame.draw.rect(self.screen, BLACK, (x_left, y, 20, 20), 1)

            text = self.font_xs.render(label, True, BLACK)
            self.screen.blit(text, (x_left + 30, y + 2))

            y += 28

        # buat kolom kanan
        y = y_right
        for label, color in items_right:
            pygame.draw.rect(self.screen, color, (x_right, y, 20, 20))
            pygame.draw.rect(self.screen, BLACK, (x_right, y, 20, 20), 1)

            text = self.font_xs.render(label, True, BLACK)
            self.screen.blit(text, (x_right + 30, y + 2))

            y += 28

    def draw_control_panel(self):
        px = 420
        py = SCREEN_HEIGHT - 250
        w = 400
        h = 170
        pygame.draw.rect(self.screen, LIGHT_BLUE, (px, py, w, h))
        pygame.draw.rect(self.screen, BLACK, (px, py, w, h), 2)
        title = self.font_s.render("Pilihan Metode:", True, BLACK)
        self.screen.blit(title, (px+12, py+8))

        algos = ["DFS","BFS","GBFS","A*"]
        gap = 90
        start_x = px + 18
        self.algo_buttons.clear()
        for i,algo in enumerate(algos):
            bx = start_x + i*gap
            rect = pygame.Rect(bx, py+40, 80, 36)
            color = GREEN if self.algorithm == algo else GRAY
            pygame.draw.rect(self.screen, color, rect)
            pygame.draw.rect(self.screen, BLACK, rect, 2)
            t = self.font_s.render(algo, True, BLACK)
            tr = t.get_rect(center=rect.center)
            self.screen.blit(t, tr)
            self.algo_buttons[algo] = rect

        # tombol "start"
        panel_width = 440 
        sr = pygame.Rect(0, 0, 220, 56)  
        sr.centerx = px + panel_width // 2
        sr.top = py + 92

        self.start_button_rect = sr
        pygame.draw.rect(self.screen, (160,255,160), sr)
        pygame.draw.rect(self.screen, BLACK, sr, 3)
        st = self.font_l.render("START", True, BLACK)
        self.screen.blit(st, st.get_rect(center=sr.center))

    def draw_info_panel(self):
        ix = SCREEN_WIDTH - 360
        iy = SCREEN_HEIGHT - 250
        w = 340
        h = 170
        pygame.draw.rect(self.screen, LIGHT_BLUE, (ix, iy, w, h))
        pygame.draw.rect(self.screen, BLACK, (ix, iy, w, h), 2)
        title = self.font_s.render("Detail Informasi:", True, BLACK)
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
                txt = self.font_xs.render(line, True, BLACK)
                self.screen.blit(txt, (ix+12, y))
                y += 26
        else:
            txt = self.font_xs.render("Pilih toko terlebih dahulu", True, DARK_GRAY)
            self.screen.blit(txt, (ix+12, iy+50))

    def draw_popup_full(self):
        # popup parkiran penuh
        w = 600
        h = 180
        x = SCREEN_WIDTH//2 - w//2
        y = SCREEN_HEIGHT//2 - h//2

        pygame.draw.rect(self.screen, ALERT_RED, (x,y,w,h))
        pygame.draw.rect(self.screen, BLACK, (x,y,w,h), 4)
        title = self.font_xl.render("SEMUA PARKIRAN PENUH!", True, WHITE)
        subtitle = self.font_l.render("Mohon maaf, tidak ada slot tersisa.", True, WHITE)
        self.screen.blit(title, (x + w//2 - title.get_width()//2, y+30))
        self.screen.blit(subtitle, (x + w//2 - subtitle.get_width()//2, y+100))

    def handle_click(self, pos):
        # cek klik toko mall
        for shop_name, (sx,sy) in self.shops.items():
            rx = self.mall_offset_x + sx*self.grid_size + 2
            ry = self.mall_offset_y + sy*self.grid_size + 2
            rect = pygame.Rect(rx, ry, self.grid_size-4, self.grid_size-4)
            if rect.collidepoint(pos):
                # pilih toko
                self.find_path(shop_name, self.algorithm)
                return

        # tombol algoritma
        for algo, rect in self.algo_buttons.items():
            if rect.collidepoint(pos):
                self.algorithm = algo
                if self.selected_shop:
                    self.find_path(self.selected_shop, self.algorithm)
                return

        # tombol "start"
        if self.start_button_rect and self.start_button_rect.collidepoint(pos):
            if self.selected_shop and self.target_parking:
                self.mark_parking_occupied()

            else:
                pass

    def load_parking_data(self):
        try:
            with open("parking_data.json", "r") as f:
                data = json.load(f)
                self.occupied_parking = {tuple(x) for x in data.get("occupied", [])}
                self.cars_entered = data.get("cars_entered", 0)
        except FileNotFoundError:
            # kalau belum ada file, mulai fresh
            self.occupied_parking = set()
            self.cars_entered = 0


    def handle_event(self, event):
        if event.type == pygame.QUIT:
            return False
        if event.type == pygame.KEYDOWN:
            if self.state == "splash":
                self.state = "map"
            else:
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
                # gambar peta dan UI
                self.animate_movement()
                self.draw_parking_layout()
                self.draw_mall_layout()
                self.draw_legend()
                self.draw_control_panel()
                self.draw_info_panel()

                # popup parkiran penuh
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
