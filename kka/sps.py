import pygame
import sys
from collections import deque, defaultdict
import heapq
import math

# Initialize Pygame
pygame.init()

# Constants
SCREEN_WIDTH = 1200
SCREEN_HEIGHT = 800
FPS = 60

# Colors
WHITE = (255, 255, 255)
BLACK = (0, 0, 0)
BLUE = (100, 150, 255)
RED = (255, 100, 100)
GREEN = (100, 255, 100)
YELLOW = (255, 255, 100)
ORANGE = (255, 165, 0)
PINK = (255, 192, 203)
LIGHT_BLUE = (173, 216, 230)
GRAY = (200, 200, 200)
DARK_GRAY = (80, 80, 80)
NAVY = (0, 0, 128)
LIGHT_GRAY = (220, 220, 220)
PURPLE = (200, 0, 200)

class SmartParkingSystem:
    def __init__(self):
        self.screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT))
        pygame.display.set_caption("Smart Parking System")
        self.clock = pygame.time.Clock()
        self.font_large = pygame.font.Font(None, 48)
        self.font_medium = pygame.font.Font(None, 32)
        self.font_small = pygame.font.Font(None, 24)
        self.font_tiny = pygame.font.Font(None, 16)
        
        self.state = "splash"  # splash, map, result
        self.animation_counter = 0
        
        # Setup parking layout
        self.setup_parking_layout()
        self.setup_shops()
        self.setup_parking_spots()
        self.setup_graph()
        
        self.selected_shop = None
        self.algorithm = "A*"  # Default algorithm
        self.path = []
        self.path_cost = 0
        self.target_parking = None
        self.blink_animation = 0
        self.start_position = (1, 7)  # Default start position (purple car)
        self.current_position = (1, 7)  # Current car position
        self.occupied_parking = set()  # Track occupied parking spots
        self.start_button_rect = None
        
    def setup_parking_layout(self):
        """Setup grid-based parking layout"""
        self.grid_size = 40
        self.grid_cols = 8
        self.grid_rows = 8
        
        # Parking layout on left side
        self.parking_offset_x = 50
        self.parking_offset_y = 120
        
        # Mall layout on right side
        self.mall_offset_x = 500
        self.mall_offset_y = 120
        
    def setup_shops(self):
        """Setup shop locations in mall grid"""
        # Format: shop_name: (row in mall grid)
        self.shops = {
            # Row 1 (y=1)
            "SOGO": {"pos": (1, 1), "entrance": "north"},
            "Watsons": {"pos": (4, 1), "entrance": "north"},
            "Wing Stop": {"pos": (7, 1), "entrance": "north"},
            # Row 2 (y=2)
            "Matahari": {"pos": (1, 2), "entrance": "west"},
            "Sephora": {"pos": (4, 2), "entrance": "north"},
            "Yoshinoya": {"pos": (7, 2), "entrance": "east"},
            # Row 3 (y=3)
            "H&M": {"pos": (1, 3), "entrance": "west"},
            "This is April": {"pos": (4, 3), "entrance": "north"},
            "Hokben": {"pos": (7, 3), "entrance": "east"},
            # Row 4 (y=4)
            "Miniso": {"pos": (1, 4), "entrance": "south"},
            "Gaudi": {"pos": (4, 4), "entrance": "south"},
            "Teazzi": {"pos": (7, 4), "entrance": "south"},
            # Row 5 (y=5)
            "ZARA": {"pos": (1, 5), "entrance": "south"},
            "HMNS": {"pos": (4, 5), "entrance": "south"},
            "Sociolla": {"pos": (7, 5), "entrance": "south"},
            # Row 6 (y=6)
            "Sour Sally": {"pos": (1, 6), "entrance": "south"},
            "Guardian": {"pos": (4, 6), "entrance": "south"},
            "Fore": {"pos": (7, 6), "entrance": "south"},
        }
        
    def setup_parking_spots(self):
        """Setup available parking spots in parking area"""
        self.initial_parking_spots = [
            (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
            (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6),
            (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6),
            (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6),
        ]
        self.parking_spots = self.initial_parking_spots.copy()
        
    def setup_graph(self):
        """Build graph for pathfinding in parking area"""
        self.graph = defaultdict(list)
        self.positions = {}
        
        # Create nodes for all walkable grid positions
        for x in range(self.grid_cols):
            for y in range(self.grid_rows):
                self.positions[(x, y)] = (
                    self.parking_offset_x + x * self.grid_size + self.grid_size // 2,
                    self.parking_offset_y + y * self.grid_size + self.grid_size // 2
                )
                
                # Connect to adjacent nodes
                for dx, dy in [(0, 1), (1, 0), (0, -1), (-1, 0)]:
                    nx, ny = x + dx, y + dy
                    if 0 <= nx < self.grid_cols and 0 <= ny < self.grid_rows:
                        #if (nx, ny) in self.occupied_parking:  # Hanya block yang sudah terisi
                        #    continue
                        
                        cost = 1
                        self.graph[(x, y)].append(((nx, ny), cost))
    
    def get_entrance_position(self, shop_name):
        """Get parking entrance based on shop entrance direction"""
        shop = self.shops[shop_name]
        entrance = shop["entrance"]
        
        # Map to parking entrance coordinates
        if entrance == "north":
            return (1, 1)  # Pintu masuk utara
        elif entrance == "south":
            return (1, 6)  # Pintu masuk selatan
        return (1, 7)
    
    def find_closest_parking(self, entrance_pos):
        """Find closest available parking spot to entrance"""
        closest = None
        min_distance = float('inf')
        
        for spot in self.parking_spots:
            if spot not in self.occupied_parking:  # Only empty spots
                distance = abs(spot[0] - entrance_pos[0]) + abs(spot[1] - entrance_pos[1])
                if distance < min_distance:
                    min_distance = distance
                    closest = spot
        
        return closest
    
    def bfs(self, start, end):
        """Breadth-First Search pathfinding"""
        queue = deque([(start, [start])])
        visited = {start}
        
        while queue:
            current, path = queue.popleft()
            if current == end:
                return path, len(path) - 1
            
            for neighbor, _ in self.graph[current]:
                if neighbor not in visited:
                    visited.add(neighbor)
                    queue.append((neighbor, path + [neighbor]))
        
        return [], 0
    
    def dijkstra(self, start, end):
        """Dijkstra's algorithm pathfinding"""
        distances = {(x, y): float('inf') for x in range(self.grid_cols) for y in range(self.grid_rows)}
        distances[start] = 0
        previous = {}
        pq = [(0, start)]
        
        while pq:
            current_dist, current = heapq.heappop(pq)
            
            if current_dist > distances[current]:
                continue
            
            if current == end:
                break
            
            for neighbor, cost in self.graph[current]:
                distance = current_dist + cost
                
                if distance < distances[neighbor]:
                    distances[neighbor] = distance
                    previous[neighbor] = current
                    heapq.heappush(pq, (distance, neighbor))
        
        path = []
        current = end
        while current in previous:
            path.append(current)
            current = previous[current]
        path.append(start)
        path.reverse()
        
        return path, distances[end]
    
    def heuristic(self, pos, target):
        """Heuristic for A*"""
        return abs(pos[0] - target[0]) + abs(pos[1] - target[1])
    
    def a_star(self, start, end):
        """A* pathfinding algorithm"""
        open_set = [(0, start)]
        came_from = {}
        g_score = {(x, y): float('inf') for x in range(self.grid_cols) for y in range(self.grid_rows)}
        g_score[start] = 0
        f_score = {(x, y): float('inf') for x in range(self.grid_cols) for y in range(self.grid_rows)}
        f_score[start] = self.heuristic(start, end)
        
        while open_set:
            _, current = heapq.heappop(open_set)
            
            if current == end:
                path = [current]
                while current in came_from:
                    current = came_from[current]
                    path.append(current)
                path.reverse()
                return path, len(path) - 1
            
            for neighbor, cost in self.graph[current]:
                tentative_g = g_score[current] + cost
                
                if tentative_g < g_score[neighbor]:
                    came_from[neighbor] = current
                    g_score[neighbor] = tentative_g
                    f_score[neighbor] = tentative_g + self.heuristic(neighbor, end)
                    heapq.heappush(open_set, (f_score[neighbor], neighbor))
        
        return [], 0
    
    def dfs(self, start, end):
        """Depth-First Search pathfinding"""
        stack = [(start, [start])]
        visited = {start}
        
        while stack:
            current, path = stack.pop()
            if current == end:
                return path, len(path) - 1
            
            for neighbor, _ in self.graph[current]:
                if neighbor not in visited:
                    visited.add(neighbor)
                    stack.append((neighbor, path + [neighbor]))
        
        return [], 0
    
    def find_path(self, shop_name, algorithm):
        """Calculate parking path based on selected algorithm"""
        entrance = self.get_entrance_position(shop_name)
        parking = self.find_closest_parking(entrance)
        
        if parking is None:
            print("No available parking spots!")
            return
        
        self.target_parking = parking
        
        if algorithm == "BFS":
            path, cost = self.bfs(self.current_position, parking)
        elif algorithm == "DFS":
            path, cost = self.dfs(self.current_position, parking)
        elif algorithm == "Dijkstra":
            path, cost = self.dijkstra(self.current_position, parking)
        else:  # A*
            path, cost = self.a_star(self.current_position, parking)
        
        self.path = path
        self.path_cost = cost
        self.selected_shop = shop_name
        self.algorithm = algorithm
    
    def mark_parking_occupied(self):
        """Mark target parking as occupied and update current position"""
        if self.target_parking:
            self.occupied_parking.add(self.target_parking)
            self.current_position = self.target_parking
            self.path = []  # Clear path after parking
    
    def draw_splash_screen(self):
        """Draw initial splash screen"""
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
        """Draw parking area layout"""
        # Draw title
        title = self.font_small.render("Layout Parkiran", True, BLACK)
        self.screen.blit(title, (self.parking_offset_x, 95))
        
        # Draw grid background
        for x in range(self.grid_cols):
            for y in range(self.grid_rows):
                rect_x = self.parking_offset_x + x * self.grid_size
                rect_y = self.parking_offset_y + y * self.grid_size
                pygame.draw.rect(self.screen, LIGHT_GRAY, (rect_x, rect_y, self.grid_size, self.grid_size), 1)
        
        # Draw parking spots - determine color based on status
        for spot in self.parking_spots:
            x, y = spot
            rect_x = self.parking_offset_x + x * self.grid_size
            rect_y = self.parking_offset_y + y * self.grid_size
            
            # Check if occupied
            if spot in self.occupied_parking:
                color = RED  # Occupied
            else:
                # Blue for empty spots
                color = BLUE
            
            pygame.draw.rect(self.screen, color, (rect_x, rect_y, self.grid_size, self.grid_size))
            pygame.draw.rect(self.screen, BLACK, (rect_x, rect_y, self.grid_size, self.grid_size), 2)
        
        # Draw entrance markers (green) - sesuai koordinat mockup
        entrance_positions = [
            (0, 0),  # Pintu masuk utara
            (0, 7),  # Pintu masuk selatan
        ]
        
        for entrance in entrance_positions:
            if entrance in self.positions:
                pos = self.positions[entrance]
                pygame.draw.circle(self.screen, GREEN, (int(pos[0]), int(pos[1])), 8)
                pygame.draw.circle(self.screen, BLACK, (int(pos[0]), int(pos[1])), 8, 2)
        
        # Draw path with navy dots
        if self.path and len(self.path) > 1:
            for i in range(len(self.path)):
                x, y = self.path[i]
                pos = self.positions[(x, y)]
                pygame.draw.circle(self.screen, NAVY, (int(pos[0]), int(pos[1])), 4)
        
        # Draw target parking with animation (pink blinking)
        if self.target_parking:
            x, y = self.target_parking
            rect_x = self.parking_offset_x + x * self.grid_size
            rect_y = self.parking_offset_y + y * self.grid_size
            
            # Blinking animation
            if (self.animation_counter // 15) % 2 == 0:
                pygame.draw.rect(self.screen, PINK, (rect_x, rect_y, self.grid_size, self.grid_size))
                pygame.draw.rect(self.screen, BLACK, (rect_x, rect_y, self.grid_size, self.grid_size), 2)
        
        # Draw current car position (purple circle) - default di (1,7)
        if self.current_position in self.positions:
            pos = self.positions[self.current_position]
            pygame.draw.circle(self.screen, PURPLE, (int(pos[0]), int(pos[1])), 12)
            pygame.draw.circle(self.screen, BLACK, (int(pos[0]), int(pos[1])), 12, 2)
    
    def draw_mall_layout(self):
        """Draw mall/shop layout"""
        # Draw title
        title = self.font_small.render("Layout Mall", True, BLACK)
        self.screen.blit(title, (self.mall_offset_x, 95))
        
        # Draw grid background for mall (3 columns x 5 rows)
        for x in range(9):
            for y in range(8):
                rect_x = self.mall_offset_x + x * self.grid_size
                rect_y = self.mall_offset_y + y * self.grid_size
                pygame.draw.rect(self.screen, LIGHT_GRAY, (rect_x, rect_y, self.grid_size, self.grid_size), 1)
        
        # Draw shops
        for shop_name, shop_info in self.shops.items():
            x, y = shop_info["pos"]
            rect_x = self.mall_offset_x + x * self.grid_size
            rect_y = self.mall_offset_y + y * self.grid_size
            
            # Highlight selected shop
            if shop_name == self.selected_shop:
                pygame.draw.rect(self.screen, ORANGE, (rect_x, rect_y, self.grid_size, self.grid_size))
            else:
                pygame.draw.rect(self.screen, YELLOW, (rect_x, rect_y, self.grid_size, self.grid_size))
            
            pygame.draw.rect(self.screen, BLACK, (rect_x, rect_y, self.grid_size, self.grid_size), 2)
            
            # Draw shop name (smaller font, wrapped)
            shop_lines = shop_name.split()
            for i, line in enumerate(shop_lines):
                if i < 2:
                    shop_text = self.font_tiny.render(line, True, BLACK)
                    self.screen.blit(shop_text, (rect_x + 3, rect_y + 5 + i * 12))
    
    def draw_legend(self):
        """Draw legend section"""
        legend_x = 30
        legend_y = SCREEN_HEIGHT - 160
        
        # Legend background
        pygame.draw.rect(self.screen, LIGHT_BLUE, (legend_x, legend_y, 320, 140))
        pygame.draw.rect(self.screen, BLACK, (legend_x, legend_y, 320, 140), 2)
        
        title = self.font_small.render("Keterangan Warna:", True, BLACK)
        self.screen.blit(title, (legend_x + 10, legend_y + 8))
        
        items = [
            ("Merah: Parkir Terisi", RED),
            ("Biru: Parkir Kosong", BLUE),
            ("Hijau: Pintu Masuk", GREEN),
            ("Pink: Target Parkir", PINK),
            ("Navy: Jalur Parkir", NAVY),
            ("Kuning: Toko", YELLOW),
            ("Orange: Target Toko", ORANGE),
        ]
        
        y_offset = legend_y + 35
        for text, color in items:
            pygame.draw.rect(self.screen, color, (legend_x + 10, y_offset, 18, 18))
            pygame.draw.rect(self.screen, BLACK, (legend_x + 10, y_offset, 18, 18), 1)
            label = self.font_tiny.render(text, True, BLACK)
            self.screen.blit(label, (legend_x + 35, y_offset + 2))
            y_offset += 22
    
    def draw_control_panel(self):
        """Draw algorithm control panel"""
        panel_x = 400
        panel_y = SCREEN_HEIGHT - 160
        panel_width = 340
        panel_height = 140
        
        pygame.draw.rect(self.screen, LIGHT_BLUE, (panel_x, panel_y, panel_width, panel_height))
        pygame.draw.rect(self.screen, BLACK, (panel_x, panel_y, panel_width, panel_height), 2)
        
        # Title
        title = self.font_small.render("Pilihan Metode:", True, BLACK)
        self.screen.blit(title, (panel_x + 15, panel_y + 8))
        
        algorithms = [
            ("DFS", 15),
            ("GBFS", 90),
            ("BFS", 165),
            ("A*", 240)
        ]
        
        for algo, x_pos in algorithms:
            button_rect = pygame.Rect(panel_x + x_pos, panel_y + 35, 70, 35)
            
            color = GREEN if self.algorithm == algo else GRAY
            pygame.draw.rect(self.screen, color, button_rect)
            pygame.draw.rect(self.screen, BLACK, button_rect, 2)
            
            text = self.font_tiny.render(algo, True, BLACK)
            text_rect = text.get_rect(center=button_rect.center)
            self.screen.blit(text, text_rect)
        
        # START button
        start_rect = pygame.Rect(panel_x + 70, panel_y + 80, 200, 45)
        self.start_button_rect = start_rect  # Store for click detection
        pygame.draw.rect(self.screen, (150, 255, 150), start_rect)
        pygame.draw.rect(self.screen, BLACK, start_rect, 3)
        start_text = self.font_medium.render("START", True, BLACK)
        start_text_rect = start_text.get_rect(center=start_rect.center)
        self.screen.blit(start_text, start_text_rect)
    
    def draw_info_panel(self):
        """Draw information panel"""
        info_x = SCREEN_WIDTH - 330
        info_y = SCREEN_HEIGHT - 160
        info_width = 300
        info_height = 140
        
        pygame.draw.rect(self.screen, LIGHT_BLUE, (info_x, info_y, info_width, info_height))
        pygame.draw.rect(self.screen, BLACK, (info_x, info_y, info_width, info_height), 2)
        
        title = self.font_small.render("Detail Informasi:", True, BLACK)
        self.screen.blit(title, (info_x + 15, info_y + 8))
        
        if self.selected_shop:
            info_texts = [
                f"Shop: {self.selected_shop}",
                f"Algorithm: {self.algorithm}",
                f"Path length (nodes): {len(self.path)}",
                f"Cost (steps): {int(self.path_cost)}",
            ]
            
            y_offset = info_y + 35
            for text in info_texts:
                label = self.font_tiny.render(text, True, BLACK)
                self.screen.blit(label, (info_x + 15, y_offset))
                y_offset += 26
        else:
            no_select = self.font_tiny.render("Pilih toko terlebih dahulu", True, DARK_GRAY)
            self.screen.blit(no_select, (info_x + 15, info_y + 50))
    
    def draw_map(self):
        """Draw parking map screen"""
        self.screen.fill(WHITE)
        
        # Draw both layouts
        self.draw_parking_layout()
        self.draw_mall_layout()
        
        # Draw panels
        self.draw_legend()
        self.draw_control_panel()
        self.draw_info_panel()
        
        self.animation_counter += 1
    
    def handle_map_click(self, pos):
        """Handle click on map to select shop or algorithm"""
        # Check mall shops
        for shop_name, shop_info in self.shops.items():
            x, y = shop_info["pos"]
            rect_x = self.mall_offset_x + x * self.grid_size
            rect_y = self.mall_offset_y + y * self.grid_size
            rect = pygame.Rect(rect_x, rect_y, self.grid_size, self.grid_size)
            
            if rect.collidepoint(pos):
                self.find_path(shop_name, self.algorithm)
                return
        
        # Check algorithm buttons
        panel_y = SCREEN_HEIGHT - 160
        algorithms = [
            ("DFS", 415),
            ("GBFS", 490),
            ("BFS", 565),
            ("A*", 640)
        ]
        
        for algo, button_x in algorithms:
            button_rect = pygame.Rect(button_x, panel_y + 35, 70, 35)
            
            if button_rect.collidepoint(pos):
                self.algorithm = algo
                if self.selected_shop:
                    self.find_path(self.selected_shop, self.algorithm)
                return
        
        # Check START button
        if self.start_button_rect and self.start_button_rect.collidepoint(pos):
            if self.selected_shop and self.target_parking:
                self.mark_parking_occupied()
    
    def handle_event(self, event):
        """Handle events"""
        if event.type == pygame.QUIT:
            return False
        
        if event.type == pygame.KEYDOWN or event.type == pygame.MOUSEBUTTONDOWN:
            if self.state == "splash":
                self.state = "map"
                self.animation_counter = 0
            elif self.state == "map":
                if event.type == pygame.MOUSEBUTTONDOWN:
                    self.handle_map_click(event.pos)
        
        return True
    
    def run(self):
        """Main loop"""
        running = True
        
        while running:
            for event in pygame.event.get():
                running = self.handle_event(event)
            
            if self.state == "splash":
                self.draw_splash_screen()
            elif self.state == "map":
                self.draw_map()
            
            pygame.display.flip()
            self.clock.tick(FPS)
        
        pygame.quit()
        sys.exit()

# Run the application
if __name__ == "__main__":
    app = SmartParkingSystem()
    app.run()
