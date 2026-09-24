import pandas as pd
import psycopg2
import os
from dotenv import load_dotenv

load_dotenv()


class DatabaseManager:

    def __init__(self):
        self.connection = psycopg2.connect(
            host="localhost",
            port=5432,
            database="u095_scraper",
            user=os.getenv("DB_USER"),
            password=os.getenv("DB_PASSWORD")
        )

    def get_pending_urls(self):
        cursor = self.connection.cursor()

        cursor.execute("""
            SELECT id, url, status
            FROM planning_urls
            WHERE status = 'Pending'
            ORDER BY id
        """)

        rows = cursor.fetchall()
        cursor.close()

        return rows

    def get_pending_dataframe(self):
        cursor = self.connection.cursor()

        cursor.execute("""
            SELECT id, url, status
            FROM planning_urls
            WHERE status = 'Pending'
            ORDER BY id
        """)

        rows = cursor.fetchall()
        cursor.close()

        return pd.DataFrame(
            rows,
            columns=["id", "Url", "Status"]
        )

    def update_url_status(self, url, status):
        cursor = self.connection.cursor()

        cursor.execute(
            """
            UPDATE planning_urls
            SET status = %s,
                updated_at = CURRENT_TIMESTAMP
            WHERE url = %s
            """,
            (status, url)
        )

        self.connection.commit()
        cursor.close()

        print(f"Updated status: {url} -> {status}")


if __name__ == "__main__":
    db = DatabaseManager()

    urls = db.get_pending_urls()

    print("Pending URLs:")

    for row in urls:
        print(row)

    if urls:
        test_url = urls[0][1]

        db.update_url_status(
            test_url,
            "Testing"
        )

    db.connection.close()